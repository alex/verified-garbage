import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.PointBatch

/-! The public batch counter survives field and table operations. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside Keeps ea_sc)

theorem tableFrame_outside {base : Addr} {o n : Nat} {m m' : Mem}
    (h : TableFrame base o n m m') (ho : 64 ≤ o) (hn : 768 ≤ o + n) :
    Outside base 64 (o + n - 64) m m' := by
  intro p hp
  exact h p (by omega) (by omega)

theorem batchBegin_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block batchBegin) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 j ∧ t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧
      (∀ r, r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 56 8 s.mem t.mem := by
  have hw : InRegions s.wr (off base 56) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have he : BitVec.ofNat 64 (j + 1) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 j := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [batchBegin, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, State.store64, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hs.rdi, hr, hw, hc, he,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, fun r hr => ?_, trivial, trivial, ?_⟩
  · exact Mem.readW_writeW_self64 _ _ _
  · simp only [hr, ite_false]
  · intro p hp
    exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by decide) p hp

theorem batchBitOffset_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j : Nat) (hj : j < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j) :
    WP isa (.block batchBitOffset) s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 (16 * j) ∧ Keeps [.rax, .rdx, .rcx, .rsi] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hv : (BitVec.ofNat 64 j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply WP.of_runBlock
  simp only [batchBitOffset, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul,
    State.load64, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hs.rdi, hr, hc, hv,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · change BitVec.ofNat 64 (j * 16) = BitVec.ofNat 64 (16 * j)
    rw [Nat.mul_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem batchTest_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j : Nat) (hj : j < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j) :
    WP isa (.block batchTest) s fun t => t.zf = some (decide (j = 0)) ∧ Keeps [.rbx] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hz : (BitVec.ofNat 64 j == 0) = decide (j = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hj]
  apply WP.of_runBlock
  simp only [batchTest, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, ea_sc, RegUpd.gpr_setReg, RegUpd.zf_arithFlags, hs.rdi, hr, hc, BitVec.and_self, hz,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

end VG.Proof.Ed25519.X86_64
