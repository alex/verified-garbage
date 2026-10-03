import VerifiedGarbage.Proof.Framework.Bitslice.Lanes

/-!
# The row domain: bitwise circuits with constants that differ by position

Like the truth-table domain (`Table.lean`), but for circuits whose constants
differ from one bit position to the next (a multiplexer tree selecting
among constant words, say): code that combines words only with `xor`, `and`
and `or` computes each bit position from the same position of its inputs
and constants. An abstract value holds the word on each of `2 ^ k` input
rows at once, in lanes of `w` bits: bit `w c + p` is bit `p` of the word on
row `c`. A constant is the same word on every row. `RowRel p c` relates the
value to bit `p` of a concrete word, on row `c`: a check of the values (one
`decide`, on `Nat` bitwise operations that the kernel evaluates natively)
proves what the code computes at each bit position, for every input.
-/

namespace VG.Bitslice

/-- Words on `2 ^ k` rows, in lanes of `w` bits; rotations and shifts move
bits between positions, so they are not represented. -/
def rows (w k : Nat) : Dom Nat w where
  xor a b := some (a ^^^ b)
  and a b := some (a &&& b)
  or a b := some (a ||| b)
  ror _ _ := none
  shr _ _ := none
  const v := some (rep w v.toNat k)

/-- Bit `p` of the word is bit `p` of the value's row `c`. -/
def RowRel {w : Nat} (p c : Nat) (a : Nat) (x : BitVec w) : Prop := a.testBit (w * c + p) = x.getLsbD p

theorem rows_sound {w k p c : Nat} (hp : p < w) (hc : c < 2 ^ k) :
    (rows w k).Sound (RowRel p c) where
  xor ha hb h := by
    simp only [rows, Option.some.injEq] at h; subst h
    simp only [RowRel, Nat.testBit_xor, BitVec.getLsbD_xor] at *; rw [ha, hb]
  and ha hb h := by
    simp only [rows, Option.some.injEq] at h; subst h
    simp only [RowRel, Nat.testBit_and, BitVec.getLsbD_and] at *; rw [ha, hb]
  or ha hb h := by
    simp only [rows, Option.some.injEq] at h; subst h
    simp only [RowRel, Nat.testBit_or, BitVec.getLsbD_or] at *; rw [ha, hb]
  ror _ h := by cases h
  shr _ h := by cases h
  const {v a} h := by
    simp only [rows, Option.some.injEq] at h; subst h
    simp only [RowRel, testBit_rep v.isLt, lane_lt hc hp, decide_true, Bool.true_and,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hp, BitVec.testBit_toNat]

end VG.Bitslice
