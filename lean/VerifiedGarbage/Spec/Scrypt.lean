import VerifiedGarbage.Spec.Pbkdf2

/-!
# scrypt (RFC 7914)

**Trusted** (as every file in `Spec/`). The password-based key derivation
function scrypt, transcribed from RFC 7914, *The scrypt Password-Based Key
Derivation Function* (August 2016); section numbers below refer to it.
Octet strings are lists of bytes, and the Salsa20/8 Core reads and writes
its sixteen 32-bit words little-endian (as Salsa20 does: Section 8 of the
Salsa20 specification the RFC cites, and the RFC's test vectors).

The contracts of the functions implemented in assembly (the Salsa20/8 Core,
scryptBlockMix and scryptROMix) are in `Spec/Scrypt/Contract.lean`; the two
PBKDF2 steps around them are composed by the caller from the verified
PBKDF2-HMAC-SHA-256.
-/

namespace VG.Spec.Scrypt

open Pbkdf2 (xorBytes)

/-- A 32-bit word. -/
abbrev Word := BitVec 32

/-! ## The Salsa20/8 Core (§3) -/

/-- One line of the RFC's `salsa20_word_specification`,
`x[i] ^= R(x[j]+x[k], n)`, where `R(a,b)` is the rotation of `a` by `b`
bits towards the high bits. -/
def step (x : Vector Word 16) (i j k : Fin 16) (n : Nat) : Vector Word 16 :=
  x.set i (x[i] ^^^ (x[j] + x[k]).rotateLeft n)

/-- The body of the RFC's loop `for (i = 8;i > 0;i -= 2)`: a column round
and a row round, in the RFC's order. -/
def doubleRound (x : Vector Word 16) : Vector Word 16 :=
  let x := step x  4  0 12  7; let x := step x  8  4  0  9
  let x := step x 12  8  4 13; let x := step x  0 12  8 18
  let x := step x  9  5  1  7; let x := step x 13  9  5  9
  let x := step x  1 13  9 13; let x := step x  5  1 13 18
  let x := step x 14 10  6  7; let x := step x  2 14 10  9
  let x := step x  6  2 14 13; let x := step x 10  6  2 18
  let x := step x  3 15 11  7; let x := step x  7  3 15  9
  let x := step x 11  7  3 13; let x := step x 15 11  7 18
  let x := step x  1  0  3  7; let x := step x  2  1  0  9
  let x := step x  3  2  1 13; let x := step x  0  3  2 18
  let x := step x  6  5  4  7; let x := step x  7  6  5  9
  let x := step x  4  7  6 13; let x := step x  5  4  7 18
  let x := step x 11 10  9  7; let x := step x  8 11 10  9
  let x := step x  9  8 11 13; let x := step x 10  9  8 18
  let x := step x 12 15 14  7; let x := step x 13 12 15  9
  let x := step x 14 13 12 13
  step x 15 14 13 18

/-- `salsa20_word_specification`: four iterations of `doubleRound` (the loop
runs for `i = 8, 6, 4, 2`), then the input added word by word (modulo 2³²). -/
def core (b : Vector Word 16) : Vector Word 16 :=
  Vector.zipWith (· + ·) (Nat.repeat doubleRound 4 b) b

/-- Word `j` of a byte string read as little-endian 32-bit integers. -/
def wordLE (bs : List Byte) (j : Nat) : Word :=
  (bs.getD (4 * j + 3) 0 ++ bs.getD (4 * j + 2) 0 ++ bs.getD (4 * j + 1) 0 ++ bs.getD (4 * j) 0 : Word)

/-- Sixteen words as 64 bytes, each little-endian. -/
def serialize (x : Vector Word 16) : List Byte :=
  x.toList.flatMap fun w => [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- `Salsa (T)`: the Salsa20/8 Core on a 64-octet string. -/
def salsa (t : List Byte) : List Byte :=
  serialize (core (Vector.ofFn fun j => wordLE t j.1))

/-! ## scryptBlockMix (§4) -/

/-- `B[i]`: the `i`th 64-octet block of `b`. -/
def blk (b : List Byte) (i : Nat) : List Byte := (b.drop (64 * i)).take 64

/-- Step 2 of scryptBlockMix, from `X` and for the blocks `B[i]` with `i` in
`is`, in order: `T = X xor B[i]`, `X = Salsa (T)`, `Y[i] = X`; the list of
the `Y[i]`. -/
def blockMixYs (b : List Byte) : List Byte → List Nat → List (List Byte)
  | _, [] => []
  | x, i :: is => let x' := salsa (xorBytes x (blk b i)); x' :: blockMixYs b x' is

/-- scryptBlockMix with block size parameter `r`, on the `128 * r` octets
`B[0] ‖ … ‖ B[2 * r - 1]`: step 1 (`X = B[2 * r - 1]`), step 2 for
`i = 0 … 2 * r - 1`, and step 3,
`B' = (Y[0], Y[2], …, Y[2 * r - 2], Y[1], Y[3], …, Y[2 * r - 1])`. -/
def blockMix (r : Nat) (b : List Byte) : List Byte :=
  let y := blockMixYs b (blk b (2 * r - 1)) (List.range (2 * r))
  ((List.range r).flatMap fun i => y.getD (2 * i) []) ++
    ((List.range r).flatMap fun i => y.getD (2 * i + 1) [])

/-! ## scryptROMix (§5) -/

/-- An octet string as a little-endian integer. -/
def leNat (bs : List Byte) : Nat := bs.foldr (fun b n => b.toNat + 256 * n) 0

/-- `Integerify (B[0] ‖ … ‖ B[2 * r - 1])`: `B[2 * r - 1]` as a
little-endian integer. -/
def integerify (r : Nat) (x : List Byte) : Nat := leNat (blk x (2 * r - 1))

/-- Step 3 of scryptROMix, `n` more iterations from `X`, with the blocks `V`
written in step 2: `j = Integerify (X) mod N`, `T = X xor V[j]`,
`X = scryptBlockMix (T)`. Returns the final `X` and the indices `j`, in the
order they were computed. -/
def mixLoop (r N : Nat) (v : List (List Byte)) : Nat → List Byte → List Byte × List Nat
  | 0, x => (x, [])
  | n + 1, x =>
    let j := integerify r x % N
    let (x', js) := mixLoop r N v n (blockMix r (xorBytes x (v.getD j [])))
    (x', j :: js)

/-- Steps 1–3 of scryptROMix with block size parameter `r` and cost
parameter `N`, on the `128 * r` octets `B`: step 2 writes
`V[i] = scryptBlockMix^i (B)` for `i = 0 … N - 1` and leaves
`X = scryptBlockMix^N (B)`; then `N` iterations of step 3. Returns the
final `X` (step 4, `B'`) and the indices `j` read in step 3. -/
def roMixAux (r N : Nat) (b : List Byte) : List Byte × List Nat :=
  let v := (List.range N).map fun i => Nat.repeat (blockMix r) i b
  mixLoop r N v N (Nat.repeat (blockMix r) N b)

/-- scryptROMix (`B'`). -/
def roMix (r N : Nat) (b : List Byte) : List Byte := (roMixAux r N b).1

/-- The indices `j = Integerify (X) mod N` that scryptROMix computes in
step 3, in order: the addresses of the blocks `V[j]` it reads depend on
them, which is how scrypt is defined (§5), so implementations may leak them
(see `Spec/Scrypt/Contract.lean`). -/
def roMixIndices (r N : Nat) (b : List Byte) : List Nat := (roMixAux r N b).2

/-! ## scrypt (§6) -/

/-- The conditions §6 puts on the parameters: `N` larger than 1, a power of
2 and less than `2^(128 * r / 8)`; `p` a positive integer at most
`((2^32 - 1) * hLen) / MFLen` with `hLen = 32` and `MFLen = 128 * r`; and
`dkLen` positive (its upper bound, `(2^32 - 1) * hLen`, is PBKDF2's, step 1
of `Pbkdf2.pbkdf2`). A positive `r` is implied by the bound on `N`. -/
def valid (N r p dkLen : Nat) : Prop :=
  1 < N ∧ N &&& (N - 1) = 0 ∧ N < 2 ^ (128 * r / 8) ∧
    0 < p ∧ p ≤ (2 ^ 32 - 1) * 32 / (128 * r) ∧ 0 < dkLen

instance (N r p dkLen : Nat) : Decidable (valid N r p dkLen) := by
  unfold valid; infer_instance

/-- `scrypt (P, S, N, r, p, dkLen)`: `none` if the parameters are not
`valid`, or if PBKDF2 rejects the derived key's length; otherwise
1. `B[0] ‖ … ‖ B[p - 1] = PBKDF2-HMAC-SHA256 (P, S, 1, p * 128 * r)`,
2. `B[i] = scryptROMix (r, B[i], N)` for `i = 0 … p - 1`,
3. `DK = PBKDF2-HMAC-SHA256 (P, B[0] ‖ … ‖ B[p - 1], 1, dkLen)`. -/
def scrypt (pw s : List Byte) (N r p dkLen : Nat) : Option (List Byte) :=
  if valid N r p dkLen then do
    let b ← Pbkdf2.pbkdf2HmacSha256 pw s 1 (p * 128 * r)
    let b' := (List.range p).flatMap fun i => roMix r N ((b.drop (128 * r * i)).take (128 * r))
    Pbkdf2.pbkdf2HmacSha256 pw b' 1 dkLen
  else none

end VG.Spec.Scrypt
