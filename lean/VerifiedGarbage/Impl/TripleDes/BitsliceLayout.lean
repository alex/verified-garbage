import VerifiedGarbage.Spec.TripleDes

/-!
# Where bitsliced DES keeps each bit

Untrusted. Bitsliced code transposes 64 blocks, loaded as little-endian
64-bit words, so that word `j` holds bit `j` of every block (bit `b` of
word `j` is bit `j` of block `b`). Bit `t` of IP(block) (`getLsbD t` of
`permute ip`) is then in word `ipWord t`: the little-endian load reverses
the bytes of the big-endian block, and IP reads bit `64 - ip[63 - t]`.
The left half `L` (bits 32–63 of IP(block)) is in the words `lWord`, the
right half `R` in the words `rWord`; no bit is moved by IP.

A round reads `R` and XORs `f(R, K)` into `L`. S-box `j`'s input bit `i`
(least significant first) is bit `inBit j i` of `E(R) ⊕ K`, so R's bit
`eBit (inBit j i)` and K's bit `inBit j i`; its output bit `i` is bit
`outBit j i` of `f`, after P.
-/

namespace VG.Impl.TripleDes.Bitslice

open VG.Spec.TripleDes

/-- The word holding bit `t` of IP(block). -/
def ipWord (t : Nat) : Nat := (64 - ip.getD (63 - t) 1) ^^^ 56

/-- The word holding bit `q` of the left half. -/
def lWord (q : Nat) : Nat := ipWord (32 + q)

/-- The word holding bit `q` of the right half. -/
def rWord (q : Nat) : Nat := ipWord q

/-- The bit of `E(R) ⊕ K` that is S-box `j`'s input bit `i`. -/
def inBit (j i : Nat) : Nat := 6 * (7 - j) + i

/-- The bit of `R` that is bit `t` of `E(R)`. -/
def eBit (t : Nat) : Nat := 32 - expansion.getD (47 - t) 1

/-- The bit of `f(R, K)` (after P) that is S-box `j`'s output bit `i`. -/
def outBit (j i : Nat) : Nat :=
  ((List.range 32).find? fun q => 32 - p.getD (31 - q) 1 == 4 * (7 - j) + i).getD 0

/-- Which half a round reads: `.ba` reads `R` (in the words `rWord`) and XORs
into `L`; `.ab` reads `L` and XORs into `R`. -/
inductive Role | ba | ab
  deriving DecidableEq, Repr

/-- The state word of bit `q` of the half the round reads. -/
def readWord : Role → Nat → Nat
  | .ba, q => rWord q
  | .ab, q => lWord q

/-- The state word of bit `q` of the half the round XORs into. -/
def writeWord : Role → Nat → Nat
  | .ba, q => lWord q
  | .ab, q => rWord q

end VG.Impl.TripleDes.Bitslice
