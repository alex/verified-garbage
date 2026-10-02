import VerifiedGarbage.Spec.TripleDes

/-!
# DES's bit permutations, as maps of bit indices

Untrusted: the proofs check everything here.

FIPS 46-3 numbers bits from 1, the most significant first; these give, for
each bit of a permutation's output (numbered from 0, the least significant
first, as `BitVec.getLsbD` does), the bit of its input it is, for every
implementation to build its code from (`Proof/CmacTripleDes/Des.lean`
proves them right).
-/

namespace VG.Impl.CmacTripleDes

/-- Bit `p` of `E(R)` is bit `expSrc p` of `R` (FIPS 46-3's E, bit 1 the
most significant). -/
def expSrc (p : Nat) : Nat := 32 - Spec.TripleDes.expansion.getD (47 - p) 1

/-- Bit `j` of `P(S)` is bit `pSrc j` of `S`, the S-boxes' outputs (box 0
in the most significant four bits). -/
def pSrc (j : Nat) : Nat := 32 - Spec.TripleDes.p.getD (31 - j) 1

/-- Bit `j` of `IP(x)` is bit `ipSrc j` of `x`. -/
def ipSrc (j : Nat) : Nat := 64 - Spec.TripleDes.ip.getD (63 - j) 1

/-- Bit `j` of `IP⁻¹(x)` is bit `fpSrc j` of `x`. -/
def fpSrc (j : Nat) : Nat := 64 - Spec.TripleDes.fp.getD (63 - j) 1

/-- The total left rotation of `C` and `D` for round key `j`. -/
def rotSum (j : Nat) : Nat := ((List.range (j + 1)).map fun i => Spec.TripleDes.rotations.getD i 0).sum

/-- Bit `v` of `PC1(key)` is bit `pc1Src v` of the key. -/
def pc1Src (v : Nat) : Nat := 64 - Spec.TripleDes.pc1.getD (55 - v) 1

/-- Bit `q` of round key `j` is bit `rkSrc j q` of the key: `PC2` of `C`
and `D` (the halves of `PC1(key)`), each rotated left by `rotSum j`. -/
def rkSrc (j q : Nat) : Nat :=
  let u := 56 - Spec.TripleDes.pc2.getD (47 - q) 1
  if 28 ≤ u then pc1Src (28 + (u - 28 + 28 - rotSum j % 28) % 28)
  else pc1Src ((u + 28 - rotSum j % 28) % 28)

end VG.Impl.CmacTripleDes
