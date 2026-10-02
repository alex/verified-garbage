import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Loop
import VerifiedGarbage.Proof.Framework.AArch64.Spill

/-! # CBC register saves, setup, and restoration -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

/-- The registers the code saves in `buf`, and where. -/
abbrev saved : List (Reg × Nat) := [(.x23, 264), (.x24, 272), (.x30, 280)]

/-- The memory after the saves. -/
abbrev savedMem (s : State) : Mem := Spill.saveMem s.mem (s.gpr .x4) s.gpr saved

theorem save_eq : Impl.Rc2.AArch64.Cbc.save = Spill.saveCode .x4 saved := rfl

theorem restore_eq : Impl.Rc2.AArch64.Cbc.restore = Spill.restoreCode .x2 saved := rfl

theorem savedMem_frame (s : State) : Frame [⟨s.gpr .x4, 512⟩] s.mem (savedMem s) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

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

end VG.Proof.Rc2.AArch64.Cbc
