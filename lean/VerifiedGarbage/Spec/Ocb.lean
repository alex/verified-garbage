import VerifiedGarbage.Spec.Aes

/-!
# OCB (RFC 7253)

**Trusted** (as every file in `Spec/`). The authenticated-encryption
algorithm OCB (OCB3), transcribed from RFC 7253, *The OCB
Authenticated-Encryption Algorithm* (May 2014); section numbers below refer
to it. Every string is a string of whole bytes here, as every
implementation we test against requires: the nonce, the associated data,
the plaintext and the tag (`TAGLEN = 8 t` for a tag of `t` bytes).

A 128-bit block is a `BitVec 128` whose most significant bit is the
string's first bit (`S[1]`, §2): the first byte of a block is its most
significant byte.

OCB is defined here for any blockcipher on 128-bit blocks, given as its
functions `ENCIPHER(K, ·)` and `DECIPHER(K, ·)` (`Cipher`), with
`L_* = ENCIPHER(K, zeros(128))` given too, which an implementation computes
once per key (`encryptWith`, `decryptWith`); `encrypt` and `decrypt` are OCB
with AES (§3.1's parameter sets), as the RFC defines them. The contracts of
the functions implemented in assembly are in `Spec/Ocb/Contract.lean`.
-/

namespace VG.Spec.Ocb

/-- A 128-bit block (§2): its first bit `S[1]` the most significant. -/
abbrev Block := BitVec 128

/-- A blockcipher function on 128-bit blocks. -/
abbrev Cipher := Block → Block

/-- The block of 16 bytes, the first byte the most significant. -/
def ofBytes (bs : List Byte) : Block :=
  BitVec.ofNat 128 (bs.foldl (fun acc b => 256 * acc + b.toNat) 0)

/-- The 16 bytes of a block, the most significant first. -/
def toBytes (x : Block) : List Byte :=
  (List.range 16).map fun i => x.extractLsb' (8 * (15 - i)) 8

/-- `n` zero bytes. -/
def zeros (n : Nat) : List Byte := List.replicate n 0

/-- `S xor T` on byte strings, as long as the shorter of the two. -/
def xor (s t : List Byte) : List Byte := List.zipWith (· ^^^ ·) s t

/-! ## Notation and basic operations (§2) -/

/-- §2, `double(S)`: `S[2..128] ‖ 0` if `S[1] = 0`, and
`(S[2..128] ‖ 0) xor (zeros(120) ‖ 10000111)` otherwise. -/
def double (s : Block) : Block := if s.msb then (s <<< 1) ^^^ 0x87 else s <<< 1

/-- `ntz` with at most `fuel` halvings. -/
def ntzAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 ∨ n % 2 = 1 then 0 else ntzAux fuel (n / 2) + 1

/-- §2, `ntz(n)` for a positive integer `n`: the number of trailing zero bits
of `n`, the largest `x` such that `2^x` divides `n` (halving `n` while it is
even, which takes fewer than `n` halvings). -/
def ntz (n : Nat) : Nat := ntzAux n n

/-- The string `S` of fewer than 16 bytes padded to a block:
`S ‖ 1 ‖ zeros(127 − bitlen(S))` (§4.1, §4.2). -/
def pad (s : List Byte) : Block := ofBytes (s ++ [0x80] ++ zeros (15 - s.length))

/-! ## Key-dependent variables (§4.1) -/

/-- `L_$ = double(L_*)`. -/
def lDollar (lstar : Block) : Block := double lstar

/-- `L_i`: `L_0 = double(L_$)` and `L_i = double(L_{i−1})`, so
`double` applied `i + 2` times to `L_*`. -/
def lAt (lstar : Block) (i : Nat) : Block := Nat.repeat double (i + 2) lstar

/-- The `i`-th 128-bit block of a string (from 0). -/
def blockAt (s : List Byte) (i : Nat) : Block := ofBytes ((s.drop (16 * i)).take 16)

/-! ## HASH (§4.1) -/

/-- §4.1, `HASH(K, A)` for the blockcipher `ciph` (`ENCIPHER(K, ·)`) with
`L_* = lstar`:
```
Sum_0 = zeros(128); Offset_0 = zeros(128)
for each 1 <= i <= m
   Offset_i = Offset_{i-1} xor L_{ntz(i)}
   Sum_i = Sum_{i-1} xor ENCIPHER(K, A_i xor Offset_i)
if bitlen(A_*) > 0 then
   Offset_* = Offset_m xor L_*
   CipherInput = (A_* || 1 || zeros(127-bitlen(A_*))) xor Offset_*
   Sum = Sum_m xor ENCIPHER(K, CipherInput)
else Sum = Sum_m
```
where `A_1, …, A_m` are the whole blocks of `A` and `A_*` the rest. -/
def hash (ciph : Cipher) (lstar : Block) (a : List Byte) : Block :=
  let m := a.length / 16
  let (sum, offset) := (List.range m).foldl (fun (sum, offset) i =>
    let offset := offset ^^^ lAt lstar (ntz (i + 1))
    (sum ^^^ ciph (blockAt a i ^^^ offset), offset)) ((0 : Block), (0 : Block))
  let rest := a.drop (16 * m)
  if rest.length > 0 then sum ^^^ ciph (pad rest ^^^ (offset ^^^ lstar)) else sum

/-! ## Encryption and decryption (§4.2, §4.3) -/

/-- §4.2, `Offset_0` for the nonce `N` and a tag of `t` bytes:
```
Nonce = num2str(TAGLEN mod 128,7) || zeros(120-bitlen(N)) || 1 || N
bottom = str2num(Nonce[123..128])
Ktop = ENCIPHER(K, Nonce[1..122] || zeros(6))
Stretch = Ktop || (Ktop[1..64] xor Ktop[9..72])
Offset_0 = Stretch[1+bottom..128+bottom]
``` -/
def offset0 (ciph : Cipher) (t : Nat) (nonce : List Byte) : Block :=
  let n : Block := (BitVec.ofNat 128 (8 * t % 128) <<< 121) |||
    ((1 : Block) <<< (8 * nonce.length)) ||| BitVec.ofNat 128 (nonce.foldl (fun acc b => 256 * acc + b.toNat) 0)
  let bottom := (n.extractLsb' 0 6).toNat
  let ktop := ciph (n &&& ~~~(63 : Block))
  let stretch : BitVec 192 := ktop ++ (ktop.extractLsb' 64 64 ^^^ ktop.extractLsb' 56 64)
  stretch.extractLsb' (64 - bottom) 128

/-- §4.2, `OCB-ENCRYPT(K, N, A, P)` for the blockcipher `ciph`
(`ENCIPHER(K, ·)`) with `L_* = lstar` and a tag of `t` bytes, returning the
encrypted plaintext `C_1 ‖ … ‖ C_m ‖ C_*` and the tag `Tag[1..TAGLEN]`
(whose concatenation is the RFC's `C`):
```
for each 1 <= i <= m
   Offset_i = Offset_{i-1} xor L_{ntz(i)}
   C_i = Offset_i xor ENCIPHER(K, P_i xor Offset_i)
   Checksum_i = Checksum_{i-1} xor P_i
if bitlen(P_*) > 0 then
   Offset_* = Offset_m xor L_*
   Pad = ENCIPHER(K, Offset_*)
   C_* = P_* xor Pad[1..bitlen(P_*)]
   Checksum_* = Checksum_m xor (P_* || 1 || zeros(127-bitlen(P_*)))
   Tag = ENCIPHER(K, Checksum_* xor Offset_* xor L_$) xor HASH(K,A)
else
   C_* = <empty string>
   Tag = ENCIPHER(K, Checksum_m xor Offset_m xor L_$) xor HASH(K,A)
```
where `P_1, …, P_m` are the whole blocks of `P`, `P_*` the rest, and
`Checksum_0 = zeros(128)`. -/
def encryptWith (ciph : Cipher) (lstar : Block) (t : Nat) (nonce a p : List Byte) :
    List Byte × List Byte :=
  let m := p.length / 16
  let (offset, checksum, c) := (List.range m).foldl (fun (offset, checksum, c) i =>
    let offset := offset ^^^ lAt lstar (ntz (i + 1))
    (offset, checksum ^^^ blockAt p i, c ++ toBytes (offset ^^^ ciph (blockAt p i ^^^ offset))))
    (offset0 ciph t nonce, (0 : Block), ([] : List Byte))
  let rest := p.drop (16 * m)
  let (c, tag) :=
    if rest.length > 0 then
      let offset := offset ^^^ lstar
      let checksum := checksum ^^^ pad rest
      (c ++ xor rest (toBytes (ciph offset)),
        ciph (checksum ^^^ offset ^^^ lDollar lstar) ^^^ hash ciph lstar a)
    else (c, ciph (checksum ^^^ offset ^^^ lDollar lstar) ^^^ hash ciph lstar a)
  (c, (toBytes tag).take t)

/-- §4.3, `OCB-DECRYPT(K, N, A, C)` for the blockcipher `ciph`
(`ENCIPHER(K, ·)`) and its inverse `inv` (`DECIPHER(K, ·)`) with
`L_* = lstar` and a tag of `t` bytes, where the RFC's `C` is the encrypted
plaintext `c` followed by the tag `T`:
```
for each 1 <= i <= m
   Offset_i = Offset_{i-1} xor L_{ntz(i)}
   P_i = Offset_i xor DECIPHER(K, C_i xor Offset_i)
   Checksum_i = Checksum_{i-1} xor P_i
if bitlen(C_*) > 0 then
   Offset_* = Offset_m xor L_*
   Pad = ENCIPHER(K, Offset_*)
   P_* = C_* xor Pad[1..bitlen(C_*)]
   Checksum_* = Checksum_m xor (P_* || 1 || zeros(127-bitlen(P_*)))
   Tag = ENCIPHER(K, Checksum_* xor Offset_* xor L_$) xor HASH(K,A)
else
   P_* = <empty string>
   Tag = ENCIPHER(K, Checksum_m xor Offset_m xor L_$) xor HASH(K,A)
if (Tag[1..TAGLEN] == T) then P = P_1 || P_2 || ... || P_m || P_* else P = INVALID
```
returning `none` for INVALID. -/
def decryptWith (ciph inv : Cipher) (lstar : Block) (t : Nat) (nonce a c tag : List Byte) :
    Option (List Byte) :=
  let m := c.length / 16
  let (offset, checksum, p) := (List.range m).foldl (fun (offset, checksum, p) i =>
    let offset := offset ^^^ lAt lstar (ntz (i + 1))
    let pi := offset ^^^ inv (blockAt c i ^^^ offset)
    (offset, checksum ^^^ pi, p ++ toBytes pi))
    (offset0 ciph t nonce, (0 : Block), ([] : List Byte))
  let rest := c.drop (16 * m)
  let (p, tag') :=
    if rest.length > 0 then
      let offset := offset ^^^ lstar
      let ps := xor rest (toBytes (ciph offset))
      let checksum := checksum ^^^ pad ps
      (p ++ ps, ciph (checksum ^^^ offset ^^^ lDollar lstar) ^^^ hash ciph lstar a)
    else (p, ciph (checksum ^^^ offset ^^^ lDollar lstar) ^^^ hash ciph lstar a)
  if (toBytes tag').take t = tag then some p else none

/-- §3, §3.1: the tag lengths in bytes (`TAGLEN` "any value up to 128" bits,
in whole bytes and not empty) and the nonce lengths in bytes (`N_MIN` = 1
byte, `N_MAX` = 15 bytes: "no more than 120 bits") that OCB is defined
for. -/
def lengthsOk (t nonceLen : Nat) : Bool := 1 ≤ t && t ≤ 16 && 1 ≤ nonceLen && nonceLen ≤ 15

/-! ## AES-OCB (§3.1) -/

/-- `ENCIPHER(K, ·)` for AES with `nr` rounds and the key schedule `w` (as
bytes). -/
def aesWith (nr : Nat) (w : List Byte) : Cipher := fun x =>
  ofBytes (Aes.cipher nr w (Vector.ofFn fun i => (toBytes x).getD i 0)).toList

/-- `DECIPHER(K, ·)` for AES with `nr` rounds and the key schedule `w` (as
bytes): the inverse cipher (FIPS 197 §5.3). -/
def aesInvWith (nr : Nat) (w : List Byte) : Cipher := fun x =>
  ofBytes (Aes.invCipher nr w (Vector.ofFn fun i => (toBytes x).getD i 0)).toList

/-- `ENCIPHER(K, ·)` for AES with the key `key` (16, 24 or 32 bytes). -/
def aes (key : List Byte) : Cipher := aesWith (Aes.rounds (key.length / 4)) (Aes.expandKey key)

/-- `DECIPHER(K, ·)` for AES with the key `key` (16, 24 or 32 bytes). -/
def aesInv (key : List Byte) : Cipher :=
  aesInvWith (Aes.rounds (key.length / 4)) (Aes.expandKey key)

/-- §4.2, AES-OCB encryption under the key `key` (16, 24 or 32 bytes) with
a tag of `t` bytes, of the plaintext `p` with the associated data `a` under
the nonce `nonce`: the RFC's ciphertext `C`, or `none` if the tag or nonce
length is not one OCB is defined for. -/
def encrypt (key : List Byte) (t : Nat) (nonce a p : List Byte) : Option (List Byte) :=
  if lengthsOk t nonce.length then
    let (c, tag) := encryptWith (aes key) (aes key 0) t nonce a p
    some (c ++ tag)
  else none

/-- §4.3, AES-OCB decryption under the key `key` (16, 24 or 32 bytes) with
a tag of `t` bytes, of the RFC's ciphertext `c` with the associated data
`a` under the nonce `nonce`: the plaintext, or `none` (INVALID) if the tag
or nonce length is not one OCB is defined for, if `c` is shorter than the
tag, or if the tag is wrong. -/
def decrypt (key : List Byte) (t : Nat) (nonce a c : List Byte) : Option (List Byte) :=
  if !lengthsOk t nonce.length || c.length < t then none
  else decryptWith (aes key) (aesInv key) (aes key 0) t nonce a (c.take (c.length - t))
    (c.drop (c.length - t))

/-! ## The key context

`vg_aes_ocb_init` stores what AES-OCB needs of a key in a 256-byte key
context, which the other AES-OCB functions read:

* bytes 0 to `16 (Nr + 1) − 1`: the AES key schedule for `Nr` rounds, as
  `vg_aes_expand_key` writes it (which the inverse cipher uses too, in
  reverse order);
* bytes 240–255: `L_* = ENCIPHER(K, zeros(128))` (§4.1).

The bytes between them (for 10 or 12 rounds) are unspecified. The functions
that read a key context compute with the ciphers of the key schedule in it,
for the number of rounds `Nr` they take as an argument, and the `L_*` in it
(`ctxCiph`, `ctxInv`, `ctxLstar`), whatever the context holds: for a
context that `vg_aes_ocb_init` wrote for `key` (`KeyRepr`), that is AES-OCB
with `key` (`encryptWith_ctx`, `decryptWith_ctx`). -/

/-- The 16 bytes at `p` as a block. -/
def blockAtMem (m : Mem) (p : Addr) : Block := ofBytes (Aes.bytesAt m p 16)

/-- `ENCIPHER(K, ·)` of the key context at `p` for `nr` rounds. -/
def ctxCiph (m : Mem) (p : Addr) (nr : Nat) : Cipher :=
  aesWith nr (Aes.bytesAt m p (16 * (nr + 1)))

/-- `DECIPHER(K, ·)` of the key context at `p` for `nr` rounds. -/
def ctxInv (m : Mem) (p : Addr) (nr : Nat) : Cipher :=
  aesInvWith nr (Aes.bytesAt m p (16 * (nr + 1)))

/-- `L_*` of the key context at `p`: its bytes 240–255. -/
def ctxLstar (m : Mem) (p : Addr) : Block := blockAtMem m (p + 240)

/-- The key context at `p` is that of the AES key `key`: it holds the key
schedule of `key` and `L_* = ENCIPHER(K, zeros(128))`. -/
def KeyRepr (m : Mem) (p : Addr) (key : List Byte) : Prop :=
  Aes.bytesAt m p (16 * (Aes.rounds (key.length / 4) + 1)) = Aes.expandKey key ∧
    ctxLstar m p = aes key 0

/-- Encryption with the key context of `key`, for its number of rounds, is
AES-OCB's with `key`. -/
theorem encryptWith_ctx {m : Mem} {p : Addr} {key : List Byte} (hk : KeyRepr m p key)
    (t : Nat) (nonce a pt : List Byte) (hl : lengthsOk t nonce.length = true) :
    encrypt key t nonce a pt =
      some ((encryptWith (ctxCiph m p (Aes.rounds (key.length / 4))) (ctxLstar m p) t nonce a
          pt).1 ++
        (encryptWith (ctxCiph m p (Aes.rounds (key.length / 4))) (ctxLstar m p) t nonce a
          pt).2) := by
  rw [ctxCiph, hk.1, hk.2, encrypt]
  simp only [hl, ↓reduceIte]
  rfl

/-- Decryption with the key context of `key`, for its number of rounds, is
AES-OCB's with `key`, for lengths that are accepted. -/
theorem decryptWith_ctx {m : Mem} {p : Addr} {key : List Byte} (hk : KeyRepr m p key)
    (t : Nat) (nonce a c tag : List Byte) (hl : lengthsOk t nonce.length = true)
    (ht : tag.length = t) :
    decrypt key t nonce a (c ++ tag) =
      decryptWith (ctxCiph m p (Aes.rounds (key.length / 4)))
        (ctxInv m p (Aes.rounds (key.length / 4))) (ctxLstar m p) t nonce a c tag := by
  have hc : (c ++ tag).length - t = c.length := by simp [ht]
  have hlt : decide ((c ++ tag).length < t) = false := by simp [ht]
  rw [ctxCiph, ctxInv, hk.1, hk.2, decrypt, hc, hl, hlt]
  simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, List.take_left,
    List.drop_left]
  rfl

end VG.Spec.Ocb
