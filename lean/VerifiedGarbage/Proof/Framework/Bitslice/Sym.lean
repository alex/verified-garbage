import VerifiedGarbage.Proof.Framework.Bitslice.Dom

/-!
# The naming domain: moves of words

Untrusted: everything here is checked by Lean.

Code that only moves words between registers and memory (loads, stores,
register copies) is tracked by naming each word: an abstract value `a` is
the word `V a`. No operation is supported, so the evaluator accepts only
moves; a check then says where each named word ends up.
-/

namespace VG.Bitslice

/-- Named words: no operations. -/
def names (w : Nat) : Dom Nat w where
  xor _ _ := none
  and _ _ := none
  or _ _ := none
  ror _ _ := none
  shr _ _ := none
  const _ := none

/-- The abstract value `a` is the word `V a`. -/
def NameRel {w : Nat} (V : Nat → BitVec w) (a : Nat) (x : BitVec w) : Prop := x = V a

theorem names_sound {w : Nat} (V : Nat → BitVec w) : (names w).Sound (NameRel V) where
  xor _ _ h := by cases h
  and _ _ h := by cases h
  or _ _ h := by cases h
  ror _ h := by cases h
  shr _ h := by cases h
  const h := by cases h

end VG.Bitslice
