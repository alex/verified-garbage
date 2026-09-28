import VerifiedGarbage.Proof.Framework.Bitslice.Dom

/-!
# The truth-table domain: bitwise circuits on all inputs at once

Untrusted: everything here is checked by Lean.

Code that combines words only with `xor`, `and`, `or` and the constants 0
and all-ones computes every bit position independently, by the same Boolean
circuit. Evaluating it once over natural numbers used as truth tables runs
the circuit on `N` inputs at once: bit `c` of an abstract value is the
circuit's value on input `c`. `TableRel p c` relates the table to bit `p`
of a concrete word, so a check of the tables (one `decide`, on `Nat`
bitwise operations that the kernel evaluates natively) proves what the
code computes at every bit position, for every input.
-/

namespace VG.Bitslice

/-- Truth tables of `N` rows: rotations and shifts are not bitwise, and
only the constants 0 and all-ones are the same at every position. -/
def table (w N : Nat) : Dom Nat w where
  xor a b := some (a ^^^ b)
  and a b := some (a &&& b)
  or a b := some (a ||| b)
  ror _ _ := none
  shr _ _ := none
  const v := if v = 0 then some 0 else if v = BitVec.allOnes w then some (2 ^ N - 1) else none

/-- Row `c` of the table is bit `p` of the word. -/
def TableRel {w : Nat} (p c : Nat) (a : Nat) (x : BitVec w) : Prop := a.testBit c = x.getLsbD p

theorem table_sound {w N p c : Nat} (hp : p < w) (hc : c < N) :
    (table w N).Sound (TableRel p c) where
  xor ha hb h := by
    simp only [table, Option.some.injEq] at h; subst h
    simp only [TableRel, Nat.testBit_xor, BitVec.getLsbD_xor] at *; rw [ha, hb]
  and ha hb h := by
    simp only [table, Option.some.injEq] at h; subst h
    simp only [TableRel, Nat.testBit_and, BitVec.getLsbD_and] at *; rw [ha, hb]
  or ha hb h := by
    simp only [table, Option.some.injEq] at h; subst h
    simp only [TableRel, Nat.testBit_or, BitVec.getLsbD_or] at *; rw [ha, hb]
  ror _ h := by cases h
  shr _ h := by cases h
  const {v a} h := by
    simp only [table] at h
    split at h
    · rename_i hv; cases h; subst hv; simp [TableRel]
    · split at h
      · rename_i hv; cases h; subst hv
        simp [TableRel, Nat.testBit_two_pow_sub_one, hc, hp]
      · cases h

/-- The table whose row `c` is `f c`, for `c < n`. -/
def tableOf (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => tableOf f n ||| (if f n then 2 ^ n else 0)

theorem testBit_tableOf (f : Nat → Bool) (n c : Nat) :
    (tableOf f n).testBit c = (decide (c < n) && f c) := by
  induction n with
  | zero => simp [tableOf]
  | succ n ih =>
    simp only [tableOf, Nat.testBit_or, ih]
    split
    · rename_i hf
      rw [Nat.testBit_two_pow]
      by_cases h : c = n
      · subst h; simp [hf]
      · have : n ≠ c := Ne.symm h
        simp only [this, decide_false, Bool.or_false]
        by_cases h' : c < n
        · simp [h', show c < n + 1 by omega]
        · simp [h', show ¬ c < n + 1 by omega]
    · rename_i hf
      simp only [Nat.zero_testBit, Bool.or_false]
      by_cases h : c = n
      · subst h; simp [hf]
      · by_cases h' : c < n
        · simp [h', show c < n + 1 by omega]
        · simp [h', show ¬ c < n + 1 by omega]

end VG.Bitslice

namespace VG.Bitslice

/-- The `w`-bit word whose bit `j` is `f j`. -/
def ofBits (w : Nat) (f : Nat → Bool) : BitVec w := BitVec.ofNat w (tableOf f w)

theorem getLsbD_ofBits (w : Nat) (f : Nat → Bool) (j : Nat) :
    (ofBits w f).getLsbD j = (decide (j < w) && f j) := by
  simp only [ofBits, BitVec.getLsbD_ofNat, testBit_tableOf]
  cases decide (j < w) <;> simp

theorem ofBits_getLsbD {w : Nat} (x : BitVec w) : ofBits w x.getLsbD = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_ofBits]; simp [hj]

end VG.Bitslice
