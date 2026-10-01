import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Loop

/-! # CBC register saves, setup, and restoration -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

def savedMem (s : State) : Mem :=
  (s.mem.writeW (s.gpr .r8 + BitVec.ofNat 64 264) (s.gpr .rbx)).writeW
    (s.gpr .r8 + BitVec.ofNat 64 272) (s.gpr .rbp)

theorem save_ok (s : State)
    (w₁ : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 264) 8)
    (w₂ : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 272) 8) :
    ∃ s', runBlock isa Impl.Rc2.X86_64.Cbc.save s = some s' ∧ Keep [] {s with mem := savedMem s} s' := by
  refine ⟨_, by
    simp only [Impl.Rc2.X86_64.Cbc.save, runBlock_cons, runStep_some, runBlock_nil,
      memOp, exec, State.store64, State.ea, offset_nat, w₁, w₂, ite_true]
    rfl, ?_⟩
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem savedMem_frame (s : State) : Frame [⟨s.gpr .r8, 512⟩] s.mem (savedMem s) := by
  exact ((Frame.refl _ _).writeW List.mem_cons_self _
    (Offset.contains_base _ (by decide : 264 + 8 ≤ 512) (by decide))).writeW List.mem_cons_self _
      (Offset.contains_base _ (by decide : 272 + 8 ≤ 512) (by decide))

theorem savedMem_rbx (s : State) : (savedMem s).readW (s.gpr .r8 + BitVec.ofNat 64 264) 64 = s.gpr .rbx := by
  rw [savedMem, Mem.readW_writeW_sep (Offset.sep _ (by decide : 264 + 8 ≤ 272 ∨ 272 + 8 ≤ 264)
    (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]

theorem savedMem_rbp (s : State) : (savedMem s).readW (s.gpr .r8 + BitVec.ofNat 64 272) 64 = s.gpr .rbp := by
  rw [savedMem, Mem.readW_writeW_self64]

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.X86_64.Cbc.setup s = some s' ∧
      s'.gpr .rbx = s.gpr .rsi ∧ s'.gpr .rbp = s.gpr .rcx ∧
      s'.gpr .rsi = s.gpr .rdx ∧ s'.gpr .rdx = s.gpr .r8 ∧
      s'.zf = some (s.gpr .rcx == 0) ∧ Keep [.rbx, .rbp, .rsi, .rdx] s s' := by
  refine ⟨_, by
    simp only [Impl.Rc2.X86_64.Cbc.setup, rr, runBlock_cons, exec, readSrc]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · rw [zf_arithFlags]
    simp [gpr_setReg]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

theorem restore_ok (s : State) (b p : BitVec 64)
    (r₁ : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 264) 8)
    (r₂ : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 272) 8)
    (v₁ : s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 264) 64 = b)
    (v₂ : s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 272) 64 = p) :
    ∃ s', runBlock isa Impl.Rc2.X86_64.Cbc.restore s = some s' ∧
      s'.gpr .rbx = b ∧ s'.gpr .rbp = p ∧ Keep [.rbx, .rbp] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [Impl.Rc2.X86_64.Cbc.restore, runBlock_cons, runStep_some,
      runBlock_nil, memOp, exec, readSrc, State.load64, State.ea, offset_nat, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, r₁, r₂, ite_true, ite_false, Option.map_some,
      v₁, v₂]
    rfl, ?_⟩
  refine ⟨?_, gpr_setReg_self _ _ _, ?_⟩
  · simp [gpr_setReg]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]

end VG.Proof.Rc2.X86_64.Cbc
