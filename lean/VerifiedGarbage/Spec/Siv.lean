import VerifiedGarbage.Spec.Cmac

/-!
# AES-SIV (RFC 5297)

**Trusted** (as every file in `Spec/`). The deterministic and nonce-based
AEAD SIV with AES (AEAD_AES_SIV_CMAC_256, `_384` and `_512`), transcribed
from RFC 5297, *Synthetic Initialization Vector (SIV) Authenticated
Encryption Using the Advanced Encryption Standard (AES)* (October 2008);
section numbers below refer to it. Every string is a string of whole bytes
here, as every implementation we test against requires.

SIV takes a key of 32, 48 or 64 bytes, split into halves `K1 ‖ K2` (§2.6):
S2V (§2.4) under `K1` computes the synthetic IV `V` from a vector of
associated data and the plaintext, using AES-CMAC (`Spec/Cmac.lean`), and
counter mode (§2.5) under `K2`, from `V` with two bits cleared, encrypts
the plaintext. For nonce-based encryption the nonce is the last component
of the associated data (§3).

The functions take AES-CMAC under `K1` as a function on byte strings
(`mac`, the PRF of S2V), and the cipher of `K2` as a function on 16-byte
blocks (`ciph`): `encryptWith`, `decryptWith`. `encrypt` and `decrypt` are
SIV with a key. S2V is computed in steps (`s2vStart`, `s2vStep`, which
absorbs one component of associated data, and `s2vFinish`, which absorbs
the last component and returns `V`), and so is the whole AEAD
(`sealWith`, `openWith` from the S2V state of the associated data): the
contracts of the functions implemented in assembly, in
`Spec/Siv/Contract.lean`, are these steps.

The RFC limits the vector of associated data to 126 components (§2.6, §7),
which the caller checks.
-/

namespace VG.Spec.Siv

open Cmac (Cipher)

/-! ## Notation (§2.1) -/

/-- `n` zero bytes. -/
def zeros (n : Nat) : List Byte := List.replicate n 0

/-- `A xor B` on byte strings. -/
def xor (a b : List Byte) : List Byte := List.zipWith (· ^^^ ·) a b

/-- `<zero>`: 128 zero bits. -/
def zero : List Byte := zeros 16

/-- `<one>`: 127 zero bits followed by a one bit. -/
def one : List Byte := zeros 15 ++ [1]

/-- §2.3, `dbl(S)`: the left shift of a 128-bit string, XORed with
`0^120 ‖ 10000111` if the bit shifted out is one, which is CMAC's doubling
(`Cmac.dbl`, SP 800-38B §6.1 steps 2–3). -/
def dbl (s : List Byte) : List Byte := Cmac.dbl 16 s

/-- §2.1, `pad(X)` for `len(X) < 128`: `X` followed by a one bit and as
many zero bits as make 128 bits. -/
def pad (x : List Byte) : List Byte := x ++ [0x80] ++ zeros (15 - x.length)

/-- §2.1, `A xorend B` for `len(A) ≥ len(B)`:
`leftmost(A, len(A) − len(B)) ‖ (rightmost(A, len(B)) xor B)`. -/
def xorend (a b : List Byte) : List Byte :=
  a.take (a.length - b.length) ++ xor (a.drop (a.length - b.length)) b

/-! ## S2V (§2.4) -/

/-- The first step of S2V: `D = AES-CMAC(K, <zero>)`. -/
def s2vStart (mac : List Byte → List Byte) : List Byte := mac zero

/-- A step of S2V's loop, absorbing the component `S` into `D`:
`D = dbl(D) xor AES-CMAC(K, S)`. -/
def s2vStep (mac : List Byte → List Byte) (d s : List Byte) : List Byte := xor (dbl d) (mac s)

/-- `D` after the components `S₁ … Sₖ`: S2V's first step and loop. -/
def s2vAcc (mac : List Byte → List Byte) (ss : List (List Byte)) : List Byte :=
  ss.foldl (s2vStep mac) (s2vStart mac)

/-- The end of S2V, with `D` and the last component `Sₙ`:
`V = AES-CMAC(K, Sₙ xorend D)` if `len(Sₙ) ≥ 128`, and
`V = AES-CMAC(K, dbl(D) xor pad(Sₙ))` otherwise. -/
def s2vFinish (mac : List Byte → List Byte) (d sn : List Byte) : List Byte :=
  if sn.length ≥ 16 then mac (xorend sn d) else mac (xor (dbl d) (pad sn))

/-- §2.4, `S2V(K, S1, …, Sn)` for the PRF `mac` (AES-CMAC under `K`):
```
if n = 0 then return V = AES-CMAC(K, <one>)
D = AES-CMAC(K, <zero>)
for i = 1 to n-1 do D = dbl(D) xor AES-CMAC(K, Si)
if len(Sn) >= 128 then T = Sn xorend D else T = dbl(D) xor pad(Sn)
return V = AES-CMAC(K, T)
``` -/
def s2v (mac : List Byte → List Byte) (ss : List (List Byte)) : List Byte :=
  match ss.getLast? with
  | none => mac one
  | some sn => s2vFinish mac (s2vAcc mac ss.dropLast) sn

/-! ## CTR (§2.5) and the AEAD (§2.6, §2.7) -/

/-- The 16 bytes of `x mod 2¹²⁸`, the most significant first. -/
def be128 (x : Nat) : List Byte := (List.range 16).map fun i => BitVec.ofNat 8 (x / 256 ^ (15 - i))

/-- The number whose big-endian bytes are `bs`. -/
def beNat (bs : List Byte) : Nat := bs.foldl (fun acc b => 256 * acc + b.toNat) 0

/-- §2.6, `Q = V bitand (1^64 ‖ 0^1 ‖ 1^31 ‖ 0^1 ‖ 1^31)`: `V` with the
31st and 63rd bits (counting from the rightmost, bit 0) cleared, the most
significant bits of its bytes 12 and 8. -/
def counter (v : List Byte) : List Byte :=
  (List.range 16).map fun i => if i = 8 ∨ i = 12 then v.getD i 0 &&& 0x7f else v.getD i 0

/-- §2.5, CTR from the counter `X`: `x` XORed with the first `len(x)` bits of
`E(K, X) ‖ E(K, X+1) ‖ E(K, X+2) ‖ …`, `X + i` the 128-bit sum modulo 2¹²⁸. -/
def ctr (ciph : Cipher) (q x : List Byte) : List Byte :=
  xor x ((List.range ((x.length + 15) / 16)).flatMap fun i => ciph (be128 (beNat q + i)))

/-- §2.6 from the S2V state `d` of the associated data (`s2vAcc mac AD`):
the synthetic IV `V = S2V(K1, AD1, …, ADn, P)` and the ciphertext
`C = P xor X`, `X` the keystream of CTR under `K2` (whose cipher is `ciph`)
from `Q`. -/
def sealWith (mac : List Byte → List Byte) (ciph : Cipher) (d p : List Byte) :
    List Byte × List Byte :=
  let v := s2vFinish mac d p
  (v, ctr ciph (counter v) p)

/-- §2.7 from the S2V state `d` of the associated data, for the synthetic IV
`v` and the ciphertext `c`: the plaintext `P = C xor X`, `X` the keystream
of CTR under `K2` from `Q`, if `T = S2V(K1, AD1, …, ADn, P)` is `V`, and
`none` (FAIL) if not. -/
def openWith (mac : List Byte → List Byte) (ciph : Cipher) (d v c : List Byte) :
    Option (List Byte) :=
  let p := ctr ciph (counter v) c
  if s2vFinish mac d p = v then some p else none

/-- §2.6, `SIV-ENCRYPT(K, P, AD1, …, ADn)` for the PRF `mac` (AES-CMAC under
`K1`) and the cipher `ciph` of `K2`, returning `V` and `C` (whose
concatenation is the RFC's output `Z = V ‖ C`):
```
V = S2V(K1, AD1, ..., ADn, P)
Q = V bitand (1^64 || 0^1 || 1^31 || 0^1 || 1^31)
C = P xor leftmost(AES(K2, Q) || AES(K2, Q+1) || ..., len(P))
``` -/
def encryptWith (mac : List Byte → List Byte) (ciph : Cipher) (ads : List (List Byte))
    (p : List Byte) : List Byte × List Byte :=
  let v := s2v mac (ads ++ [p])
  (v, ctr ciph (counter v) p)

/-- §2.7, `SIV-DECRYPT(K, Z, AD1, …, ADn)` for the PRF `mac` (AES-CMAC under
`K1`) and the cipher `ciph` of `K2`, with `Z = V ‖ C` given as `v` and `c`:
```
Q = V bitand (1^64 || 0^1 || 1^31 || 0^1 || 1^31)
P = C xor leftmost(AES(K2, Q) || AES(K2, Q+1) || ..., len(C))
T = S2V(K1, AD1, ..., ADn, P)
if T = V then return P else return FAIL
``` -/
def decryptWith (mac : List Byte → List Byte) (ciph : Cipher) (ads : List (List Byte))
    (v c : List Byte) : Option (List Byte) :=
  let p := ctr ciph (counter v) c
  if s2v mac (ads ++ [p]) = v then some p else none

/-- Encryption is its steps: S2V of the associated data, then `sealWith`. -/
theorem encryptWith_eq (mac : List Byte → List Byte) (ciph : Cipher) (ads : List (List Byte))
    (p : List Byte) : encryptWith mac ciph ads p = sealWith mac ciph (s2vAcc mac ads) p := by
  simp [encryptWith, sealWith, s2v]

/-- Decryption is its steps: S2V of the associated data, then `openWith`. -/
theorem decryptWith_eq (mac : List Byte → List Byte) (ciph : Cipher) (ads : List (List Byte))
    (v c : List Byte) : decryptWith mac ciph ads v c = openWith mac ciph (s2vAcc mac ads) v c := by
  simp [decryptWith, openWith, s2v]

/-! ## AES-SIV -/

/-- AES-CMAC under the AES key `k` (RFC 4493, SP 800-38B with AES): the
whole 128-bit MAC. -/
def cmac (k : List Byte) : List Byte → List Byte := Cmac.macFull (Cmac.aes k) 16

/-- §2.6, SIV-AES encryption under the key `key` (32, 48 or 64 bytes,
`K1 = leftmost(K, len(K)/2)`, `K2 = rightmost(K, len(K)/2)`) of the
plaintext `p` with the associated data `ads`: `Z = V ‖ C`. -/
def encrypt (key : List Byte) (ads : List (List Byte)) (p : List Byte) : List Byte :=
  let k1 := key.take (key.length / 2)
  let k2 := key.drop (key.length / 2)
  let (v, c) := encryptWith (cmac k1) (Cmac.aes k2) ads p
  v ++ c

/-- §2.7, SIV-AES decryption under the key `key` (32, 48 or 64 bytes) of
`Z = V ‖ C` with the associated data `ads`: the plaintext, or `none` (FAIL)
if `Z` is shorter than `V` or `V` is wrong. -/
def decrypt (key : List Byte) (ads : List (List Byte)) (z : List Byte) : Option (List Byte) :=
  let k1 := key.take (key.length / 2)
  let k2 := key.drop (key.length / 2)
  if z.length < 16 then none else decryptWith (cmac k1) (Cmac.aes k2) ads (z.take 16) (z.drop 16)

/-! ## With the CMAC subkeys given -/

/-- SP 800-38B §6.2, the 128-bit CMAC of the message `m` with the cipher
`ciph` and the subkeys `k1`, `k2` given (steps 2–6, step 1 having computed
them): `Cmac.macFull` with its subkeys (`macFull_eq`). -/
def cmacWith (ciph : Cipher) (k1 k2 m : List Byte) : List Byte :=
  let n := if m.length = 0 then 1 else (m.length + 16 - 1) / 16
  let ms := (List.range (n - 1)).map fun i => (m.drop (16 * i)).take 16
  Cmac.chain ciph (Cmac.zeros 16) (ms ++ [Cmac.lastBlock 16 k1 k2 (m.drop (16 * (n - 1)))])

/-- AES-CMAC is `cmacWith` with its subkeys. -/
theorem macFull_eq (ciph : Cipher) (m : List Byte) :
    Cmac.macFull ciph 16 m = cmacWith ciph (Cmac.subkeys ciph 16).1 (Cmac.subkeys ciph 16).2 m :=
  rfl

/-! ## The key context

`vg_aes_siv_init` stores what AES-SIV needs of a key `K = K1 ‖ K2` in a
512-byte key context, which the other AES-SIV functions read:

* bytes 0 to `16 (Nr + 1) − 1`: the AES key schedule of `K1` for `Nr`
  rounds, as `vg_aes_expand_key` writes it;
* bytes 240–271: the CMAC subkeys of `K1`, `K1' ‖ K2'` (SP 800-38B §6.1);
  bytes 0–271 are laid out as `vg_cmac_aes_finalize`'s `key` reads them;
* bytes 272 to `272 + 16 (Nr + 1) − 1`: the AES key schedule of `K2`.

The bytes between them (for 10 or 12 rounds) are unspecified. The functions
that read a key context compute with the CMAC and the cipher it stores, for
the number of rounds `Nr` they take as an argument (`ctxMac`, `ctxCiph`),
whatever the context holds: for a context that `vg_aes_siv_init` wrote for
`key` (`KeyRepr`), that is AES-SIV with `key` (`ctxMac_eq`,
`ctxCiph_eq`). -/

/-- AES with `nr` rounds and the key schedule in the first `16 (nr + 1)`
bytes at `p`. -/
def schedCiph (m : Mem) (p : Addr) (nr : Nat) : Cipher :=
  Cmac.aesWith nr (Aes.bytesAt m p (16 * (nr + 1)))

/-- The PRF of S2V of the key context at `p` for `nr` rounds: CMAC with the
cipher of its first key schedule and its subkeys. -/
def ctxMac (m : Mem) (p : Addr) (nr : Nat) : List Byte → List Byte :=
  cmacWith (schedCiph m p nr) (Aes.bytesAt m (p + 240) 16) (Aes.bytesAt m (p + 256) 16)

/-- The cipher of CTR of the key context at `p` for `nr` rounds: AES with
its second key schedule. -/
def ctxCiph (m : Mem) (p : Addr) (nr : Nat) : Cipher := schedCiph m (p + 272) nr

/-- The key context at `p` is that of the AES-SIV key `key` (32, 48 or 64
bytes): the key schedule of `K1`, its CMAC subkeys and the key schedule of
`K2`. -/
def KeyRepr (m : Mem) (p : Addr) (key : List Byte) : Prop :=
  let k1 := key.take (key.length / 2)
  let k2 := key.drop (key.length / 2)
  let n := 16 * (Aes.rounds (key.length / 8) + 1)
  let ks := Cmac.subkeys (Cmac.aes k1) 16
  (key.length = 32 ∨ key.length = 48 ∨ key.length = 64) ∧
    Aes.bytesAt m p n = Aes.expandKey k1 ∧
    Aes.bytesAt m (p + 240) 16 = ks.1 ∧ Aes.bytesAt m (p + 256) 16 = ks.2 ∧
    Aes.bytesAt m (p + 272) n = Aes.expandKey k2

/-- The PRF of the key context of `key`, for its number of rounds, is
AES-CMAC under `K1`. -/
theorem ctxMac_eq {m : Mem} {p : Addr} {key : List Byte} (hk : KeyRepr m p key) :
    ctxMac m p (Aes.rounds (key.length / 8)) = cmac (key.take (key.length / 2)) := by
  obtain ⟨hl, h1, hs1, hs2, -⟩ := hk
  have hr : key.length / 8 = (key.take (key.length / 2)).length / 4 := by
    simp only [List.length_take]; omega
  funext x
  rw [ctxMac, schedCiph, h1, hs1, hs2, cmac, macFull_eq, Cmac.aes, ← hr]

/-- The cipher of the key context of `key`, for its number of rounds, is AES
under `K2`. -/
theorem ctxCiph_eq {m : Mem} {p : Addr} {key : List Byte} (hk : KeyRepr m p key) :
    ctxCiph m p (Aes.rounds (key.length / 8)) = Cmac.aes (key.drop (key.length / 2)) := by
  obtain ⟨hl, -, -, -, h2⟩ := hk
  have hr : key.length / 8 = (key.drop (key.length / 2)).length / 4 := by
    simp only [List.length_drop]; omega
  rw [ctxCiph, schedCiph, h2, Cmac.aes, ← hr]

end VG.Spec.Siv
