import VerifiedGarbage.Proof.Framework.Bitslice.Dom

/-!
# The variable domain: words as XORs of whole words

Code that only moves words between registers and memory and XORs them
(loading a bitsliced word, XORing a key mask into it, storing a result) is
tracked exactly by writing each word as the XOR of some of the words it
started from (*variables*, numbered from 0). An abstract value is the set of
variables, as a natural number whose bit `v` says whether variable `v` is in
the XOR; XOR is then `^^^` on these numbers, which the kernel evaluates
natively. Only the constant 0 is known, and `and`, `or`, rotations and
shifts are not tracked.

`VarRel V N` relates abstract to concrete words, for the values `V` of the
variables below `N`.
-/

namespace VG.Bitslice

/-- The XOR of the words `V v` for the variables `v < n` in the set `a`. -/
def xorSet {w : Nat} (V : Nat → BitVec w) (a : Nat) : Nat → BitVec w
  | 0 => 0
  | n + 1 => xorSet V a n ^^^ (if a.testBit n then V n else 0)

theorem xorSet_xor {w : Nat} (V : Nat → BitVec w) (a b : Nat) (n : Nat) :
    xorSet V (a ^^^ b) n = xorSet V a n ^^^ xorSet V b n := by
  induction n with
  | zero => simp [xorSet]
  | succ n ih =>
    simp only [xorSet, ih, Nat.testBit_xor]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor]
    cases a.testBit n <;> cases b.testBit n <;>
      cases (xorSet V a n).getLsbD i <;> cases (xorSet V b n).getLsbD i <;>
      cases (V n).getLsbD i <;> simp_all

theorem xorSet_zero {w : Nat} (V : Nat → BitVec w) (n : Nat) : xorSet V 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [xorSet, ih]

theorem xorSet_two_pow {w : Nat} (V : Nat → BitVec w) {v n : Nat} (hv : v < n) :
    xorSet V (2 ^ v) n = V v := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [xorSet, Nat.testBit_two_pow]
    by_cases h : v = n
    · subst h
      have : xorSet V (2 ^ v) v = 0 := by
        have key : ∀ m ≤ v, xorSet V (2 ^ v) m = 0 := by
          intro m hm
          induction m with
          | zero => rfl
          | succ m ihm =>
            simp only [xorSet, Nat.testBit_two_pow, ihm (by omega)]
            have : v ≠ m := by omega
            simp [this]
        exact key v (Nat.le_refl _)
      simp [this]
    · rw [ih (by omega)]
      simp [h]

/-- Words as sets of variables: only XOR and the constant 0. -/
def vars (w : Nat) : Dom Nat w where
  xor a b := some (a ^^^ b)
  and _ _ := none
  or _ _ := none
  ror _ _ := none
  shr _ _ := none
  const v := if v = 0 then some 0 else none

/-- The word is the XOR of the variables below `N` in the set. -/
def VarRel {w : Nat} (V : Nat → BitVec w) (N : Nat) (a : Nat) (x : BitVec w) : Prop :=
  x = xorSet V a N

theorem vars_sound {w : Nat} (V : Nat → BitVec w) (N : Nat) : (vars w).Sound (VarRel V N) where
  xor ha hb h := by
    simp only [vars, Option.some.injEq] at h; subst h
    simp only [VarRel] at *; rw [ha, hb, xorSet_xor]
  and _ _ h := by cases h
  or _ _ h := by cases h
  ror _ h := by cases h
  shr _ h := by cases h
  const {v c} h := by
    simp only [vars] at h
    split at h
    · rename_i hv; cases h; subst hv; simp [VarRel, xorSet_zero]
    · cases h

end VG.Bitslice
