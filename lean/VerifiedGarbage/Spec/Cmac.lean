import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Spec.TripleDes

/-!
# CMAC (NIST SP 800-38B)

**Trusted** (as every file in `Spec/`). The CMAC mode for authentication,
transcribed from NIST SP 800-38B, *Recommendation for Block Cipher Modes of
Operation: The CMAC Mode for Authentication* (May 2005, updated October
2016); section numbers below refer to it. RFC 4493 specifies the same
algorithm for AES-128 (AES-CMAC).

CMAC is defined here for any block cipher, given as its forward function
`CIPH_K` on blocks of `b` bytes (`Cipher`): `b = 16` for AES and `b = 8`
for TDEA, the two block sizes §5.3 defines `R_b` for. Bit strings are
sequences of whole bytes here: every length (of the message and of the
MAC) is a multiple of 8 bits, as every implementation we test against
requires. A block's first byte holds its leftmost (most significant) bits.

The instances are `aesCmac` for AES and `tdesCmac` for TDEA (Triple DES,
`Spec/TripleDes.lean`). The primitives implemented in assembly are the
subkey generation (§6.1), the chaining of whole blocks (§6.2 step 6,
`chain`) and the last block (§6.2 steps 4 and 6); their contracts are in
`Spec/Cmac/Contract.lean` (AES) and `Spec/Cmac/TripleDesContract.lean`
(TDEA). For AES there is also streaming AES-CMAC built from them (`init`,
`absorb` and `finish`, on the streaming state `Repr`), which takes the key
and the message in pieces of any length. Truncating the MAC (§6.2 step 7)
and comparing MACs (§6.3) is the caller's (Rust's) job.
-/

namespace VG.Spec.Cmac

/-- A block cipher's forward function `CIPH_K` (§5.1), on blocks of `b`
bytes. -/
abbrev Cipher := List Byte → List Byte

/-! ## Operations (§4.2) -/

/-- `0ˢ` for `s = 8 n`: `n` zero bytes. -/
def zeros (n : Nat) : List Byte := List.replicate n 0

/-- `X ⊕ Y`, the bitwise exclusive-OR of two strings of the same length. -/
def xor (x y : List Byte) : List Byte := List.zipWith (· ^^^ ·) x y

/-- `X << 1`: the string `X` shifted left by one bit, the leftmost bit
discarded and a 0 bit entering on the right. As bytes, byte `i` becomes its
low 7 bits followed by the leftmost bit of byte `i + 1` (0 for the last
byte). -/
def shiftLeft1 (x : List Byte) : List Byte :=
  List.zipWith (fun (a c : Byte) => (a <<< 1) ||| (c >>> 7)) x (x.drop 1 ++ [0])

/-- `MSB₁(X)`: the leftmost bit of `X`. -/
def msb1 (x : List Byte) : Bool := (x.headD 0).msb

/-! ## Subkeys (§5.3, §6.1) -/

/-- §5.3, `R_b` for blocks of `b` bytes: `R₁₂₈ = 0¹²⁰10000111` for 16-byte
blocks and `R₆₄ = 0⁵⁹11011` for 8-byte blocks. -/
def rb (b : Nat) : List Byte := zeros (b - 1) ++ [if b = 8 then 0x1b else 0x87]

/-- §6.1 steps 2 and 3: `X << 1` if `MSB₁(X) = 0`, and `(X << 1) ⊕ R_b`
otherwise. -/
def dbl (b : Nat) (x : List Byte) : List Byte :=
  if msb1 x then xor (shiftLeft1 x) (rb b) else shiftLeft1 x

/-- §6.1, `SUBK(K)`, the subkeys `(K1, K2)`:
```
1. L = CIPH_K(0ᵇ)
2. If MSB₁(L) = 0, then K1 = L << 1; else K1 = (L << 1) ⊕ R_b
3. If MSB₁(K1) = 0, then K2 = K1 << 1; else K2 = (K1 << 1) ⊕ R_b
``` -/
def subkeys (ciph : Cipher) (b : Nat) : List Byte × List Byte :=
  let l := ciph (zeros b)
  let k1 := dbl b l
  (k1, dbl b k1)

/-! ## MAC generation (§6.2) -/

/-- §6.2 step 6 continued from the block `c` over the blocks `ms`: for
each block `Mᵢ`, `Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)`. Step 6 itself starts from
`C₀ = 0ᵇ` (step 5). -/
def chain (ciph : Cipher) (c : List Byte) (ms : List (List Byte)) : List Byte :=
  ms.foldl (fun c m => ciph (xor c m)) c

/-- The blocks of `b` bytes of a string whose length is a multiple of `b`. -/
def blocks (b : Nat) (m : List Byte) : List (List Byte) :=
  (List.range (m.length / b)).map fun i => (m.drop (b * i)).take b

/-- §6.2 step 4, the last block `Mₙ` from `Mₙ*` (at most `b` bytes) and the
subkeys `K1` and `K2`: `K1 ⊕ Mₙ*` if `Mₙ*` is a complete block, and
`K2 ⊕ (Mₙ* ‖ 10ʲ)` otherwise, where `j = nb − Mlen − 1` (the padding fills
the block). -/
def lastBlock (b : Nat) (k1 k2 last : List Byte) : List Byte :=
  if last.length = b then xor k1 last
  else xor k2 (last ++ [0x80] ++ zeros (b - last.length - 1))

/-- §6.2, `CMAC(K, M, Tlen)` with `Tlen = b` (the whole of `Cₙ`; `mac` is
the MAC of step 7 truncated to `t` bytes), for the message `M` (`m`):
```
1. Apply the subkey generation process in Sect. 6.1 to K to produce K1 and K2.
2. If Mlen = 0, let n = 1; else, let n = ⌈Mlen/b⌉.
3. Let M1, M2, ... , Mn-1, Mn* denote the unique sequence of bit strings such that
   M = M1 ‖ M2 ‖ ... ‖ Mn-1 ‖ Mn*, where M1, M2,..., Mn-1 are complete blocks.
4. If Mn* is a complete block, let Mn = K1 ⊕ Mn*;
   else, let Mn = K2 ⊕ (Mn* ‖ 10ʲ), where j = nb - Mlen - 1.
5. Let C0 = 0ᵇ.
6. For i = 1 to n, let Ci = CIPH_K(Ci-1 ⊕ Mi).
7. Let T = MSB_Tlen(Cn).
``` -/
def macFull (ciph : Cipher) (b : Nat) (m : List Byte) : List Byte :=
  let (k1, k2) := subkeys ciph b
  let n := if m.length = 0 then 1 else (m.length + b - 1) / b
  let ms := (List.range (n - 1)).map fun i => (m.drop (b * i)).take b
  let mn := lastBlock b k1 k2 (m.drop (b * (n - 1)))
  chain ciph (zeros b) (ms ++ [mn])

/-- §6.2 step 7, the MAC `T = MSB_Tlen(Cₙ)` of `t ≤ b` bytes. -/
def mac (ciph : Cipher) (b t : Nat) (m : List Byte) : List Byte :=
  (macFull ciph b m).take t

/-- §6.3, MAC verification: whether `T'` is `MSB_Tlen(Cₙ)` for the message
`M'`, with `Tlen` the length of `T'` (at most `b` bytes). -/
def verify (ciph : Cipher) (b : Nat) (m t : List Byte) : Bool :=
  t.length ≤ b && mac ciph b t.length m == t

/-! ## AES-CMAC -/

/-- `CIPH_K` for AES with `nr` rounds and the key schedule `w` (as bytes),
on 16-byte blocks. -/
def aesWith (nr : Nat) (w : List Byte) : Cipher := fun x =>
  (Aes.cipher nr w (Vector.ofFn fun i => x.getD i 0)).toList

/-- `CIPH_K` for AES with the key `key` (16, 24 or 32 bytes). -/
def aes (key : List Byte) : Cipher :=
  aesWith (Aes.rounds (key.length / 4)) (Aes.expandKey key)

/-- AES-CMAC: the CMAC of `m` under the AES key `key` (16, 24 or 32 bytes),
with a MAC of `t ≤ 16` bytes. -/
def aesCmac (key : List Byte) (t : Nat) (m : List Byte) : List Byte := mac (aes key) 16 t m

/-! ## TDEA-CMAC -/

/-- `CIPH_K` for TDEA (FIPS 46-3, `TripleDes.encryptBlock`) with the
schedule `k` (the three DES schedules), on 8-byte blocks. -/
def tdesWith (k : TripleDes.Schedule) : Cipher := fun x =>
  (TripleDes.encryptBlock k (Vector.ofFn fun i => x.getD i 0)).toList

/-- `CIPH_K` for TDEA with the key `key` (16 bytes, `K1 ‖ K2` with
`K3 = K1`, or 24 bytes, `K1 ‖ K2 ‖ K3`). -/
def tdes (key : List Byte) : Cipher := tdesWith (TripleDes.expandKey key)

/-- TDEA-CMAC (3DES-CMAC): the CMAC of `m` under the TDEA key `key` (16 or
24 bytes), with a MAC of `t ≤ 8` bytes. -/
def tdesCmac (key : List Byte) (t : Nat) (m : List Byte) : List Byte := mac (tdes key) 8 t m

/-! ## On memory -/

/-- The `n` blocks of `b` bytes at `p`. -/
def blocksAt (m : Mem) (p : Addr) (b n : Nat) : List (List Byte) :=
  (List.range n).map fun i => Aes.bytesAt m (p + BitVec.ofNat 64 (b * i)) b

/-! ## Streaming AES-CMAC

The streaming functions MAC a message given in pieces of any length. §6.2
cannot process a block until it knows whether it is the last (step 4 masks
the last block `Mₙ` with `K1` or `K2`), so the state holds back the
message's last bytes `Mₙ*`, between 1 and 16 of them (none for the empty
message), even a whole block, and chains the blocks before them
(`chainedLen`).

The state is 304 bytes (`[u64; 38]`):

* bytes 0–239: the AES key schedule, `16 (Nr + 1)` bytes as
  `vg_aes_expand_key` writes it (the rest of the 240 bytes is
  unspecified);
* bytes 240–271: the subkeys `K1 ‖ K2` (§6.1);
* bytes 272–287: the chaining value `Cᵢ` (§6.2 step 6) of the blocks
  chained so far, from `C₀ = 0¹²⁸` (step 5);
* bytes 288–303: the bytes held back, of which the first
  `msg.length - chainedLen 16 msg.length` are specified.

Bytes 0–271 are laid out as `vg_cmac_aes_finalize`'s `key` reads them. -/

/-- The number of bytes of a message of `len` bytes, in blocks of `b`
bytes, that §6.2 chains before its last block: those of the complete blocks
`M₁ … Mₙ₋₁` of step 3, `b (n - 1)` bytes for the `n` of step 2
(`⌈len/b⌉`, or 1 for the empty message, as `macFull` computes it). The
other bytes are `Mₙ*`. -/
def chainedLen (b len : Nat) : Nat := b * ((len + b - 1) / b - 1)

/-- The streaming state at `p` represents the message `msg` under the AES
key `key`: the key is 16, 24 or 32 bytes, and the state holds its key
schedule, its subkeys, the chaining value of the first
`chainedLen 16 msg.length` bytes of `msg` from the zero block, and the rest
of `msg` (see above). The rest of the state is unspecified. -/
def Repr (mem : Mem) (p : Addr) (key msg : List Byte) : Prop :=
  let ks := subkeys (aes key) 16
  let c := chainedLen 16 msg.length
  (key.length = 16 ∨ key.length = 24 ∨ key.length = 32) ∧
    Aes.bytesAt mem p (16 * (Aes.rounds (key.length / 4) + 1)) = Aes.expandKey key ∧
    Aes.bytesAt mem (p + 240) 32 = ks.1 ++ ks.2 ∧
    Aes.bytesAt mem (p + 272) 16 = chain (aes key) (zeros 16) (blocks 16 (msg.take c)) ∧
    Aes.bytesAt mem (p + 288) (msg.length - c) = msg.drop c

end VG.Spec.Cmac
