import VerifiedGarbage.Proof.Aes.Ct32.Bitsliced
import VerifiedGarbage.Proof.Framework.Bitslice.Atoms

/-!
# The linear layers of bitsliced AES on 32-bit words, as atoms

Untrusted: everything here is checked by Lean.

What each linear layer of the bitsliced AES of `Ct32/Bitsliced.lean`
computes, bit by bit, on input words given as atoms
(`Framework/Bitslice/Atoms.lean`; bit `t` of input word `i` is atom
`32 i + t`): output word `j`'s bit `p` is the XOR of the atoms `g j p`. The
targets' proofs check their code against these by evaluation. Position
`p = 8r + 2c + b` of a word of the bitsliced state is byte `r + 4c` of
block `b`.
-/

namespace VG.Proof.Aes.Ct32

open VG.Bitslice

/-- `toBs`: bit `j` of byte `i` of block `b`, from bit `8 (i mod 4) + j`
of word `b + 2 ⌊i / 4⌋`. -/
def toBsG (j p : Nat) : List Nat := [32 * (p % 2 + 2 * (idx p / 4)) + (8 * (idx p % 4) + j)]

/-- `fromBs`: the inverse. -/
def fromBsG (k t : Nat) : List Nat := [32 * (t % 8) + pos (k % 2) (t / 8 + 4 * (k / 2))]

def srG (j p : Nat) : List Nat := [32 * j + srSrc p]

/-- MixColumns: the bits `mcTerms`, as atoms. -/
def mcG (j p : Nat) : List Nat := (mcTerms j p).map fun wt => 32 * wt.1 + wt.2

/-- AddRoundKey: the round key is input words `8 … 15`. -/
def arkG (j p : Nat) : List Nat := [32 * j + p, 32 * (8 + j) + p]

theorem xorBits_map (W : Nat → BitVec 32) (l : List (Nat × Nat)) (hl : ∀ wt ∈ l, wt.2 < 32) :
    xorBits W (l.map fun wt => 32 * wt.1 + wt.2) = termsXor W l := by
  induction l with
  | nil => rfl
  | cons wt l ih =>
    simp only [List.map_cons, xorBits_cons, termsXor, List.foldr_cons] at ih ⊢
    rw [bitOf_word _ _ _ (hl wt (by simp)), ih fun v hv => hl v (by simp [hv])]

end VG.Proof.Aes.Ct32
