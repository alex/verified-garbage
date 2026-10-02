import VerifiedGarbage.Proof.X448.X86_64.Ops

/-!
# X448 on x86-64: loop counters

Setting and decrementing public counters without changing memory or the other
registers.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64

/-- `rbx = k`. -/
theorem setRbx_ok (s : State) (k : Nat) (hk : k < 2 ^ 32) :
    WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 k))]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨?_, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega)]

/-- `rbx -= 1`, from `rbx = k + 1`: the flag `ZF` says whether `k = 0`. -/
theorem decRbx_ok {s : State} {k : Nat} (hk : k < 2 ^ 32)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (k + 1)) :
    WP isa (.block [.alu .sub .rbx (.imm 1)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (decide (k = 0)) := by
  have hb' : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 k := by
    have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [hb, e1, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have zf : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rfl
    · rw [decide_eq_false (by omega)]
      apply beq_false_of_ne
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by simp; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left', hb', RegUpd.gpr_setReg_self, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, zf]
  exact ⟨trivial, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false,
    RegUpd.gpr_arithFlags], trivial, trivial, trivial, trivial⟩

end VG.Proof.X448.X86_64
