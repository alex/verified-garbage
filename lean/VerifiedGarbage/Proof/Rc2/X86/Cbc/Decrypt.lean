import VerifiedGarbage.Proof.Rc2.X86.Cbc.Frame

/-! # One CBC decryption step, retaining the original ciphertext -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86 VG.Impl.Rc2.X86

abbrev stashR (s : State) : Region := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 256, 8⟩

theorem stash_sub (s : State) : Region.Sub (stashR s) (bufR s) :=
  Offset.sub_base _ (by decide)

theorem call_stash {d : Spec.Rc2.Direction} {s s' : State} (hp : StepPre s) (h : CallPost d s s') :
    Spec.Rc2.blockAt s'.mem (stashR s).base = Spec.Rc2.blockAt s.mem (stashR s).base := by
  apply blockAt_frame h.mem
  have sep : (stashR s).Disjoint ⟨addr32 (s.gpr .ebp), 256⟩ := by
    have h := Offset.disjoint (addr32 (s.gpr .ebp)) (d := 256) (n := 8) (e := 0) (k := 256)
      (by omega) (by decide) (by decide)
    simpa using h
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right (stash_sub s)).symm) (And.intro sep
      (hp.stackBuf.sub_right (stash_sub s)).symm)

theorem decryptStep_ok (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.X86.Cbc.step .decrypt) s (StepPost .decrypt s) := by
  rw [Impl.Rc2.X86.Cbc.step]
  apply WP.seq
  apply WP.mono (copy64_ok s .esi .ebp 0 256 (by decide) (by decide)
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
    exact ⟨⟨addr32 (s.gpr .ebp), 264⟩, by simp [stepWrites], Offset.sub_base _ (by decide)⟩
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ := blockAt_frame frame₁ (addr32 (s.gpr .esi)) (by simpa using hp.dataBuf.sub_right (stash_sub s))
  have iv₁ := blockAt_frame frame₁ (addr32 (s.gpr .ecx)) (by simpa using hp.ivBuf.sub_right (stash_sub s))
  have stash₁ : Spec.Rc2.blockAt s₁.mem (stashR s).base = Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)) := by
    rw [keep₁.mem]; exact blockAt_copy _ _ _
  apply WP.seq
  apply WP.mono (call_ok .decrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .esi (by decide), pin₁.reg .ebx (by decide), key₁, data₁] at output₂
  have iv₂ := h₂.iv hp₁
  rw [pin₁.reg .ecx (by decide), iv₁] at iv₂
  have stash₂ := call_stash hp₁ h₂
  simp only [pin₁.reg .ebp (by decide)] at stash₂
  have stash₂' := stash₂.trans stash₁
  change WP isa (.block (Impl.Rc2.X86.Cbc.xor64 .esi .ecx ++
    Impl.Rc2.X86.Cbc.copy64 .ebp .ecx 256 0)) s₂ _
  rw [WP.block_append_iff]
  apply WP.mono (xor64_ok s₂ .esi .ecx (by decide) (by decide)
    (by simpa using hp₂.dataFit) hp₂.ivFit hp₂.readData hp₂.readIv hp₂.writeData)
  intro s₃ keep₃
  have frame₃ : Frame [dataR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  have pin₀₃ := pin₂.trans pin₃
  have hp₃ := pin₀₃.pre hp
  have data₃ : Spec.Rc2.blockAt s₃.mem (addr32 (s.gpr .esi)) =
      Spec.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx)))
        (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) := by
    have h : Spec.Rc2.blockAt s₃.mem (addr32 (s₂.gpr .esi)) =
        Spec.Rc2.xorBlock (Spec.Rc2.blockAt s₂.mem (addr32 (s₂.gpr .esi))) (Spec.Rc2.blockAt s₂.mem (addr32 (s₂.gpr .ecx))) := by
      rw [keep₃.mem]; exact blockAt_xor _ _ _
    rw [pin₂.reg .esi (by decide), pin₂.reg .ecx (by decide), output₂, iv₂] at h
    exact h
  have stash₃ := blockAt_frame frame₃ (stashR s₂).base
    (by simpa using (hp₂.dataBuf.sub_right (stash_sub s₂)).symm)
  simp only [pin₂.reg .ebp (by decide)] at stash₃
  have stash₃' := stash₃.trans stash₂'
  apply WP.mono (copy64_ok s₃ .ebp .ecx 256 0 (by decide) (by decide)
    (by have := hp₃.bufFit; omega) (by simpa using hp₃.ivFit) (hp₃.readBuf 256 (by decide)) (by simpa using hp₃.writeIv))
  intro s₄ keep₄
  simp only [BitVec.add_zero] at keep₄
  have frame₄ : Frame [ivR s₃] s₃.mem s₄.mem := by
    rw [keep₄.mem]; exact frame_store64 _ _ _
  have pin₄ := Pinned.of_keep keep₄ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  refine ⟨pin₀₃.trans pin₄, ?_, ?_⟩
  · have same := blockAt_frame frame₄ (addr32 (s₃.gpr .esi)) (by simpa using hp₃.ivData.symm)
    rw [pin₀₃.reg .esi (by decide)] at same
    exact same.trans data₃
  · have out : Spec.Rc2.blockAt s₄.mem (addr32 (s₃.gpr .ecx)) = Spec.Rc2.blockAt s₃.mem (stashR s₃).base := by
      rw [keep₄.mem]; exact blockAt_copy _ _ _
    simp only [pin₀₃.reg .ecx (by decide), pin₀₃.reg .ebp (by decide)] at out
    exact out.trans stash₃'

end VG.Proof.Rc2.X86.Cbc
