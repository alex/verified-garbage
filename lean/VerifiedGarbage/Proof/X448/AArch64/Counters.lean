import VerifiedGarbage.Proof.X448.AArch64.Ops

/-!
# X448 on AArch64: loop counters

Setting and decrementing public counters preserves memory and every other
register.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64

/-- Set the ladder or squaring counter. -/
theorem setCounter_ok (s : State) (k : Nat) (hk : k < 2 ^ 16) :
    WP isa (.block [.movz .x .x19 (BitVec.ofNat 16 k) 0]) s fun s' =>
      s'.gpr .x19 = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .x19 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => by simp only [RegUpd.gpr_write, hr, ite_false], rfl, rfl, rfl⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega)]

/-- Decrement the counter; the result is zero precisely on the last iteration. -/
theorem decCounter_ok {s : State} {k : Nat} (hk : k < 2 ^ 16)
    (hb : s.gpr .x19 = BitVec.ofNat 64 (k + 1)) :
    WP isa (.block [.subImm .x .x19 .x19 1]) s fun s' =>
      s'.gpr .x19 = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .x19 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ (s'.gpr .x19 == 0) = decide (k = 0) := by
  have hb' : s.gpr .x19 - BitVec.ofNat 64 1 = BitVec.ofNat 64 k := by
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have zero : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rfl
    · rw [decide_eq_false (by omega)]
      apply beq_false_of_ne
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by simp; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Nat.reduceLT, ite_true,
    State.read, BitVec.setWidth_eq, hb', RegUpd.gpr_write_self, zero,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [RegUpd.gpr_write, hr, ite_false], rfl, rfl, rfl, trivial⟩

end VG.Proof.X448.AArch64
