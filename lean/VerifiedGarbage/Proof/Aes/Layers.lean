import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms

/-!
# The linear layers of bitsliced AES, as atoms

Untrusted: everything here is checked by Lean.

What each linear layer of the bitsliced AES computes, bit by bit, on input
words given as atoms (`Framework/Bitslice/Atoms.lean`; bit `t` of input
word `i` is atom `64 i + t`): output word `j`'s bit `p` is the XOR of the
atoms `g j p`. The targets' proofs check their code against these by
evaluation. Position `p = 16r + 4c + b` of a word of the bitsliced state is
byte `r + 4c` of block `b`.
-/

namespace VG.Proof.Aes

open VG.Bitslice

/-- `toBs`: bit `j` of byte `i` of block `b`, from bit `8 (i mod 8) + j`
of word `b + 4 ⌊i / 8⌋`. -/
def toBsG (j p : Nat) : List Nat := [64 * (p % 4 + 4 * (idx p / 8)) + (8 * (idx p % 8) + j)]

/-- `fromBs`: the inverse. -/
def fromBsG (k t : Nat) : List Nat := [64 * (t % 8) + pos (k % 4) (t / 8 + 8 * (k / 4))]

def srG (j p : Nat) : List Nat := [64 * j + srSrc p]

/-- MixColumns: the bits `mcTerms`, as atoms. -/
def mcG (j p : Nat) : List Nat := (mcTerms j p).map fun wt => 64 * wt.1 + wt.2

/-- AddRoundKey: the round key is input words `8 … 15`. -/
def arkG (j p : Nat) : List Nat := [64 * j + p, 64 * (8 + j) + p]

theorem xorBits_map (W : Nat → BitVec 64) (l : List (Nat × Nat)) (hl : ∀ wt ∈ l, wt.2 < 64) :
    xorBits W (l.map fun wt => 64 * wt.1 + wt.2) = termsXor W l := by
  induction l with
  | nil => rfl
  | cons wt l ih =>
    simp only [List.map_cons, xorBits_cons, termsXor, List.foldr_cons] at ih ⊢
    rw [bitOf_word _ _ _ (hl wt (by simp)), ih fun v hv => hl v (by simp [hv])]

end VG.Proof.Aes
