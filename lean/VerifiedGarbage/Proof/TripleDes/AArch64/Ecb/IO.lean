import VerifiedGarbage.Proof.TripleDes.AArch64.Ecb.Loop

/-! # ECB register saves, setup, and restoration -/

namespace VG.Proof.TripleDes.AArch64.Ecb

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Proof.Rc2.AArch64 (Keep)

def savedMem (s : State) : Mem :=
  (s.mem.writeW (s.gpr .x3 + BitVec.ofNat 64 512) (s.gpr .x23)).writeW
    (s.gpr .x3 + BitVec.ofNat 64 520) (s.gpr .x30)

theorem save_ok (s : State)
    (w₁ : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 512) 8)
    (w₃ : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 520) 8) :
    ∃ s', runBlock isa Impl.TripleDes.AArch64.Ecb.save s = some s' ∧ Keep [] {s with mem := savedMem s} s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.AArch64.Ecb.save, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, Size.bytes, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true, Option.bind_some,
      State.store, State.read, BitVec.setWidth_eq, w₁, w₃]
    rfl, ?_⟩
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem savedMem_frame (s : State) : Frame [⟨s.gpr .x3, 1024⟩] s.mem (savedMem s) :=
  ((Frame.refl _ _).writeW List.mem_cons_self _
    (Offset.contains_base _ (by decide : 512 + 8 ≤ 1024) (by decide))).writeW List.mem_cons_self _
      (Offset.contains_base _ (by decide : 520 + 8 ≤ 1024) (by decide))

theorem savedMem_counter (s : State) : (savedMem s).readW (s.gpr .x3 + BitVec.ofNat 64 512) 64 = s.gpr .x23 := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 512 + 8 ≤ 520 ∨ 520 + 8 ≤ 512)
    (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]

theorem savedMem_link (s : State) : (savedMem s).readW (s.gpr .x3 + BitVec.ofNat 64 520) 64 = s.gpr .x30 := by
  rw [savedMem, Mem.readW_writeW_self64]

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.TripleDes.AArch64.Ecb.setup s = some s' ∧
      s'.gpr .x23 = s.gpr .x2 ∧ s'.gpr .x2 = s.gpr .x3 ∧ Keep [.x23, .x2] s s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.AArch64.Ecb.setup, rr, runBlock_cons, exec]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr.1, hr.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

theorem restore_ok (s : State) (b lr : BitVec 64)
    (r₁ : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 512) 8)
    (r₃ : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 520) 8)
    (v₁ : s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 512) 64 = b)
    (v₃ : s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 520) 64 = lr) :
    ∃ s', runBlock isa Impl.TripleDes.AArch64.Ecb.restore s = some s' ∧
      s'.gpr .x23 = b ∧ s'.gpr .x30 = lr ∧ Keep [.x23, .x30] s s' := by
  change s.mem.read _ 8 = b at v₁
  change s.mem.read _ 8 = lr at v₃
  refine ⟨_, by
    simp only [Impl.TripleDes.AArch64.Ecb.restore, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, Size.bytes, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true, Option.bind_some,
      State.load, BitVec.setWidth_eq, gpr_write, mem_write, rd_write, wr_write,
      r₁, r₃, reduceCtorEq, ite_false, Option.map_some, v₁, v₃]
    rfl, ?_⟩
  refine ⟨?_, gpr_write_self _ _ _ _, ?_⟩
  · simp [gpr_write, BitVec.setWidth_eq]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr.1, hr.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

theorem LoopPost.scratchRead {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : LoopPost d s n s') (hp : StepPre s n) (i : Nat) (hi : 512 ≤ i ∧ i + 8 ≤ 1024) :
    s'.mem.readW (s.gpr .x2 + BitVec.ofNat 64 i) 64 =
      s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 i) 64 := by
  have sub : Region.Sub ⟨s.gpr .x2 + BitVec.ofNat 64 i, 8⟩ (bufR s) :=
    Offset.sub_base _ hi.2
  have sep : (Region.mk (s.gpr .x2 + BitVec.ofNat 64 i) 8).Disjoint ⟨s.gpr .x2, 512⟩ :=
    Offset.disjoint_base _ (by omega) (by omega)
  apply h.mem.readW (r := ⟨s.gpr .x2 + BitVec.ofNat 64 i, 8⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right sub).symm) sep

end VG.Proof.TripleDes.AArch64.Ecb
