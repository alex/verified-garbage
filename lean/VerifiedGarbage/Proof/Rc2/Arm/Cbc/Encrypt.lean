import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Frame

/-! # One CBC encryption step -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

theorem encryptStep_ok (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.Arm.Cbc.step .encrypt) s (StepPost .encrypt s) := by
  rw [Impl.Rc2.Arm.Cbc.step]
  apply WP.seq
  apply WP.mono (xor64_ok s .r1 .r4 (by decide) (by decide)
    (by simpa using hp.dataFit) hp.ivFit hp.readData hp.readIv hp.writeData)
  intro s₁ keep₁
  have pin₁ := Pinned.of_keep keep₁ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ : Spec.Rc2.blockAt s₁.mem (State.addr (s.gpr .r1)) =
      Spec.Rc2.xorBlock (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) := by
    rw [keep₁.mem]; exact blockAt_xor _ _ _
  apply WP.seq
  apply WP.mono (call_ok .encrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .r1 (by decide), pin₁.reg .r0 (by decide), key₁, data₁] at output₂
  apply WP.mono (copy64_ok s₂ .r1 .r4 0 0 (by decide) (by decide)
    (by simpa using hp₂.dataFit) (by simpa using hp₂.ivFit) (by simpa using hp₂.readData) (by simpa using hp₂.writeIv))
  intro s₃ keep₃
  simp only [BitVec.add_zero] at keep₃
  have frame₃ : Frame [ivR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  refine ⟨pin₂.trans pin₃, ?_, ?_⟩
  · have same := blockAt_frame frame₃ (State.addr (s₂.gpr .r1)) (by simpa using hp₂.ivData.symm)
    rw [pin₂.reg .r1 (by decide)] at same
    exact same.trans output₂
  · have out : Spec.Rc2.blockAt s₃.mem (State.addr (s₂.gpr .r4)) = Spec.Rc2.blockAt s₂.mem (State.addr (s₂.gpr .r1)) := by
      rw [keep₃.mem]; exact blockAt_copy _ _ _
    rw [pin₂.reg .r4 (by decide), pin₂.reg .r1 (by decide)] at out
    exact out.trans output₂

end VG.Proof.Rc2.Arm.Cbc
