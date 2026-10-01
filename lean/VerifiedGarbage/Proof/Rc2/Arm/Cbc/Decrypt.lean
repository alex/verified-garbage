import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Frame

/-! # One CBC decryption step, retaining the original ciphertext -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

abbrev stashR (s : State) : Region := ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 256, 8⟩

theorem stash_sub (s : State) : Region.Sub (stashR s) (bufR s) :=
  Offset.sub_base _ (by decide)

theorem call_stash {d : Spec.Rc2.Direction} {s s' : State} (hp : StepPre s) (h : CallPost d s s') :
    Spec.Rc2.blockAt s'.mem (stashR s).base = Spec.Rc2.blockAt s.mem (stashR s).base := by
  apply blockAt_frame h.mem
  have sep : (stashR s).Disjoint ⟨State.addr (s.gpr .r2), 256⟩ := by
    have h := Offset.disjoint (State.addr (s.gpr .r2)) (d := 256) (n := 8) (e := 0) (k := 256)
      (by omega) (by decide) (by decide)
    simpa using h
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right (stash_sub s)).symm) sep

theorem decryptStep_ok (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.Arm.Cbc.step .decrypt) s (StepPost .decrypt s) := by
  rw [Impl.Rc2.Arm.Cbc.step]
  apply WP.seq
  apply WP.mono (copy64_ok s .r1 .r2 0 256 (by decide) (by decide)
    (by simpa using hp.dataFit) (by have := hp.bufFit; omega) (by simpa using hp.readData) (hp.writeBuf 256 (by decide)))
  intro s₁ keep₁
  simp only [BitVec.add_zero] at keep₁
  have frame₁ : Frame [stashR s] s.mem s₁.mem := by
    rw [keep₁.mem]; exact frame_store64 _ _ _
  have pin₁ : Pinned s s₁ := by
    apply Pinned.of_keep keep₁
    apply (frame_store64 _ _ _).sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨State.addr (s.gpr .r2), 264⟩, by simp [stepWrites], Offset.sub_base _ (by decide)⟩
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ := blockAt_frame frame₁ (State.addr (s.gpr .r1)) (by simpa using hp.dataBuf.sub_right (stash_sub s))
  have iv₁ := blockAt_frame frame₁ (State.addr (s.gpr .r4)) (by simpa using hp.ivBuf.sub_right (stash_sub s))
  have stash₁ : Spec.Rc2.blockAt s₁.mem (stashR s).base = Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)) := by
    rw [keep₁.mem]; exact blockAt_copy _ _ _
  apply WP.seq
  apply WP.mono (call_ok .decrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .r1 (by decide), pin₁.reg .r0 (by decide), key₁, data₁] at output₂
  have iv₂ := h₂.iv hp₁
  rw [pin₁.reg .r4 (by decide), iv₁] at iv₂
  have stash₂ := call_stash hp₁ h₂
  simp only [pin₁.reg .r2 (by decide)] at stash₂
  have stash₂' := stash₂.trans stash₁
  change WP isa (.block (Impl.Rc2.Arm.Cbc.xor64 .r1 .r4 ++
    Impl.Rc2.Arm.Cbc.copy64 .r2 .r4 256 0)) s₂ _
  rw [WP.block_append_iff]
  apply WP.mono (xor64_ok s₂ .r1 .r4 (by decide) (by decide)
    (by simpa using hp₂.dataFit) hp₂.ivFit hp₂.readData hp₂.readIv hp₂.writeData)
  intro s₃ keep₃
  have frame₃ : Frame [dataR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  have pin₀₃ := pin₂.trans pin₃
  have hp₃ := pin₀₃.pre hp
  have data₃ : Spec.Rc2.blockAt s₃.mem (State.addr (s.gpr .r1)) =
      Spec.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0)))
        (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1)))) (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r4))) := by
    have h : Spec.Rc2.blockAt s₃.mem (State.addr (s₂.gpr .r1)) =
        Spec.Rc2.xorBlock (Spec.Rc2.blockAt s₂.mem (State.addr (s₂.gpr .r1))) (Spec.Rc2.blockAt s₂.mem (State.addr (s₂.gpr .r4))) := by
      rw [keep₃.mem]; exact blockAt_xor _ _ _
    rw [pin₂.reg .r1 (by decide), pin₂.reg .r4 (by decide), output₂, iv₂] at h
    exact h
  have stash₃ := blockAt_frame frame₃ (stashR s₂).base
    (by simpa using (hp₂.dataBuf.sub_right (stash_sub s₂)).symm)
  simp only [pin₂.reg .r2 (by decide)] at stash₃
  have stash₃' := stash₃.trans stash₂'
  apply WP.mono (copy64_ok s₃ .r2 .r4 256 0 (by decide) (by decide)
    (by have := hp₃.bufFit; omega) (by simpa using hp₃.ivFit) (hp₃.readBuf 256 (by decide)) (by simpa using hp₃.writeIv))
  intro s₄ keep₄
  simp only [BitVec.add_zero] at keep₄
  have frame₄ : Frame [ivR s₃] s₃.mem s₄.mem := by
    rw [keep₄.mem]; exact frame_store64 _ _ _
  have pin₄ := Pinned.of_keep keep₄ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  refine ⟨pin₀₃.trans pin₄, ?_, ?_⟩
  · have same := blockAt_frame frame₄ (State.addr (s₃.gpr .r1)) (by simpa using hp₃.ivData.symm)
    rw [pin₀₃.reg .r1 (by decide)] at same
    exact same.trans data₃
  · have out : Spec.Rc2.blockAt s₄.mem (State.addr (s₃.gpr .r4)) = Spec.Rc2.blockAt s₃.mem (stashR s₃).base := by
      rw [keep₄.mem]; exact blockAt_copy _ _ _
    simp only [pin₀₃.reg .r4 (by decide), pin₀₃.reg .r2 (by decide)] at out
    exact out.trans stash₃'

end VG.Proof.Rc2.Arm.Cbc
