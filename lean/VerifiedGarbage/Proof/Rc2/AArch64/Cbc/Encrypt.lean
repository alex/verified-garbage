import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Frame

/-! # One CBC encryption step -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem encryptStep_ok (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.AArch64.Cbc.step .encrypt) s (StepPost .encrypt s) := by
  rw [Impl.Rc2.AArch64.Cbc.step]
  apply WP.seq
  obtain ⟨s₁, run₁, keep₁⟩ := xor64_ok s .x1 .x23 (by decide) (by decide)
    hp.readData hp.readIv hp.writeData
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have pin₁ := Pinned.of_keep keep₁ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ : Spec.Rc2.blockAt s₁.mem (s.gpr .x1) =
      Spec.Rc2.xorBlock (Spec.Rc2.blockAt s.mem (s.gpr .x1)) (Spec.Rc2.blockAt s.mem (s.gpr .x23)) := by
    rw [keep₁.mem]; exact blockAt_xor _ _ _
  apply WP.seq
  apply WP.mono (call_ok .encrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .x1 (by decide), pin₁.reg .x0 (by decide), key₁, data₁] at output₂
  obtain ⟨s₃, run₃, keep₃⟩ := copy64_ok s₂ .x1 .x23 0 0 (by decide)
    (by simpa using hp₂.readData) (by simpa using hp₂.writeIv)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  simp only [BitVec.add_zero] at keep₃
  have frame₃ : Frame [ivR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  refine ⟨pin₂.trans pin₃, ?_, ?_⟩
  · have same := blockAt_frame frame₃ (s₂.gpr .x1) (by simpa using hp₂.ivData.symm)
    rw [pin₂.reg .x1 (by decide)] at same
    exact same.trans output₂
  · have out : Spec.Rc2.blockAt s₃.mem (s₂.gpr .x23) = Spec.Rc2.blockAt s₂.mem (s₂.gpr .x1) := by
      rw [keep₃.mem]; exact blockAt_copy _ _ _
    rw [pin₂.reg .x23 (by decide), pin₂.reg .x1 (by decide)] at out
    exact out.trans output₂

end VG.Proof.Rc2.AArch64.Cbc
