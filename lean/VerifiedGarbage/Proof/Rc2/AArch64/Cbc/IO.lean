import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Loop

/-! # CBC register saves, setup, and restoration -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

def savedMem (s : State) : Mem :=
  ((s.mem.writeW (s.gpr .x4 + BitVec.ofNat 64 264) (s.gpr .x23)).writeW
    (s.gpr .x4 + BitVec.ofNat 64 272) (s.gpr .x24)).writeW
      (s.gpr .x4 + BitVec.ofNat 64 280) (s.gpr .x30)

theorem save_ok (s : State)
    (w₁ : InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 264) 8)
    (w₂ : InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 272) 8)
    (w₃ : InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 280) 8) :
    ∃ s', runBlock isa Impl.Rc2.AArch64.Cbc.save s = some s' ∧ Keep [] {s with mem := savedMem s} s' := by
  refine ⟨_, by
    simp only [Impl.Rc2.AArch64.Cbc.save, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, Size.bytes, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true, Option.bind_some,
      State.store, State.read, BitVec.setWidth_eq, w₁, w₂, w₃]
    rfl, ?_⟩
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem savedMem_frame (s : State) : Frame [⟨s.gpr .x4, 512⟩] s.mem (savedMem s) := by
  exact (((Frame.refl _ _).writeW List.mem_cons_self _
    (Offset.contains_base _ (by decide : 264 + 8 ≤ 512) (by decide))).writeW List.mem_cons_self _
      (Offset.contains_base _ (by decide : 272 + 8 ≤ 512) (by decide))).writeW List.mem_cons_self _
      (Offset.contains_base _ (by decide : 280 + 8 ≤ 512) (by decide))

theorem savedMem_rbx (s : State) : (savedMem s).readW (s.gpr .x4 + BitVec.ofNat 64 264) 64 = s.gpr .x23 := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 8 ≤ 280 ∨ 280 + 8 ≤ 264)
    (by decide) (by decide)) (by decide), Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 8 ≤ 272 ∨ 272 + 8 ≤ 264)
    (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]

theorem savedMem_rbp (s : State) : (savedMem s).readW (s.gpr .x4 + BitVec.ofNat 64 272) 64 = s.gpr .x24 := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 272 + 8 ≤ 280 ∨ 280 + 8 ≤ 272)
    (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]

theorem savedMem_link (s : State) : (savedMem s).readW (s.gpr .x4 + BitVec.ofNat 64 280) 64 = s.gpr .x30 := by
  rw [savedMem, Mem.readW_writeW_self64]

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.AArch64.Cbc.setup s = some s' ∧
      s'.gpr .x23 = s.gpr .x1 ∧ s'.gpr .x24 = s.gpr .x3 ∧
      s'.gpr .x1 = s.gpr .x2 ∧ s'.gpr .x2 = s.gpr .x4 ∧
      zeroCount s' = some (s.gpr .x3 == 0) ∧ Keep [.x23, .x24, .x1, .x2] s s' := by
  refine ⟨_, by
    simp only [Impl.Rc2.AArch64.Cbc.setup, rr, runBlock_cons, exec]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · unfold zeroCount
    simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

theorem restore_ok (s : State) (b p lr : BitVec 64)
    (r₁ : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 264) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 272) 8)
    (r₃ : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 280) 8)
    (v₁ : s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 264) 64 = b)
    (v₂ : s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 272) 64 = p)
    (v₃ : s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 280) 64 = lr) :
    ∃ s', runBlock isa Impl.Rc2.AArch64.Cbc.restore s = some s' ∧
      s'.gpr .x23 = b ∧ s'.gpr .x24 = p ∧ s'.gpr .x30 = lr ∧ Keep [.x23, .x24, .x30] s s' := by
  change s.mem.read _ 8 = b at v₁
  change s.mem.read _ 8 = p at v₂
  change s.mem.read _ 8 = lr at v₃
  refine ⟨_, by
    simp only [Impl.Rc2.AArch64.Cbc.restore, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, Size.bytes, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true, Option.bind_some,
      State.load, BitVec.setWidth_eq, gpr_write, mem_write, rd_write, wr_write,
      r₁, r₂, r₃, reduceCtorEq, ite_false, Option.map_some, v₁, v₂, v₃]
    rfl, ?_⟩
  refine ⟨?_, ?_, gpr_write_self _ _ _ _, ?_⟩
  · simp [gpr_write, BitVec.setWidth_eq]
  · simp [gpr_write, BitVec.setWidth_eq]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr.1, hr.2.1, hr.2.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

end VG.Proof.Rc2.AArch64.Cbc
