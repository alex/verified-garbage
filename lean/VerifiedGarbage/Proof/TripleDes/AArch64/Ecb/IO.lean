import VerifiedGarbage.Proof.TripleDes.AArch64.Ecb.Loop
import VerifiedGarbage.Proof.Framework.AArch64.Spill

/-! # ECB register saves, setup, and restoration -/

namespace VG.Proof.TripleDes.AArch64.Ecb

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Proof.Rc2.AArch64 (Keep)

/-- The registers the code saves in `buf`, and where. -/
abbrev saved : List (Reg × Nat) := [(.x23, 512), (.x30, 520)]

/-- The memory after the saves. -/
abbrev savedMem (s : State) : Mem := Spill.saveMem s.mem (s.gpr .x3) s.gpr saved

theorem save_eq : Impl.TripleDes.AArch64.Ecb.save = Spill.saveCode .x3 saved := rfl

theorem restore_eq : Impl.TripleDes.AArch64.Ecb.restore = Spill.restoreCode .x2 saved := rfl

theorem savedMem_frame (s : State) : Frame [⟨s.gpr .x3, 1024⟩] s.mem (savedMem s) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

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
