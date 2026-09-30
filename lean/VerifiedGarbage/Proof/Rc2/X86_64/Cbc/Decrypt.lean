import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Frame

/-! # One CBC decryption step, retaining the original ciphertext -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64 VG.Impl.Rc2.X86_64

abbrev stashR (s : State) : Region := ⟨s.gpr .rdx + BitVec.ofNat 64 256, 8⟩

theorem stash_sub (s : State) : Region.Sub (stashR s) (bufR s) :=
  Offset.sub_base _ (by decide)

theorem call_stash {d : Spec.Rc2.Direction} {s s' : State} (hp : StepPre s) (h : CallPost d s s') :
    Spec.Rc2.blockAt s'.mem (stashR s).base = Spec.Rc2.blockAt s.mem (stashR s).base := by
  apply blockAt_frame h.mem
  have sep : (stashR s).Disjoint ⟨s.gpr .rdx, 256⟩ := by
    have h := Offset.disjoint (s.gpr .rdx) (d := 256) (n := 8) (e := 0) (k := 256)
      (by omega) (by decide) (by decide)
    simpa using h
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right (stash_sub s)).symm) (And.intro sep
      ((hp.stackBuf.sub_right (stash_sub s)).symm))

theorem decryptStep_ok (s : State) (hp : StepPre s) :
    WP isa (Impl.Rc2.X86_64.Cbc.step .decrypt) s (StepPost .decrypt s) := by
  rw [Impl.Rc2.X86_64.Cbc.step]
  apply WP.seq
  obtain ⟨s₁, run₁, keep₁⟩ := copy64_ok s .rsi .rdx 0 256 (by decide)
    (by simpa using hp.readData) (hp.writeBuf 256 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  simp only [BitVec.add_zero] at keep₁
  have frame₁ : Frame [stashR s] s.mem s₁.mem := by
    rw [keep₁.mem]; exact frame_store64 _ _ _
  have pin₁ : Pinned s s₁ := by
    apply Pinned.of_keep keep₁
    apply (frame_store64 _ _ _).sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨⟨s.gpr .rdx, 264⟩, by simp [stepWrites], Offset.sub_base _ (by decide)⟩
  have hp₁ := pin₁.pre hp
  have key₁ := pin₁.schedule hp
  have data₁ := blockAt_frame frame₁ (s.gpr .rsi) (by simpa using hp.dataBuf.sub_right (stash_sub s))
  have iv₁ := blockAt_frame frame₁ (s.gpr .rbx) (by simpa using hp.ivBuf.sub_right (stash_sub s))
  have stash₁ : Spec.Rc2.blockAt s₁.mem (stashR s).base = Spec.Rc2.blockAt s.mem (s.gpr .rsi) := by
    rw [keep₁.mem]; exact blockAt_copy _ _ _
  apply WP.seq
  apply WP.mono (call_ok .decrypt s₁ hp₁.call)
  intro s₂ h₂
  have pin₂ := pin₁.trans (Pinned.of_call h₂)
  have hp₂ := pin₂.pre hp
  have output₂ := h₂.output
  rw [pin₁.reg .rsi (by decide), pin₁.reg .rdi (by decide), key₁, data₁] at output₂
  have iv₂ := h₂.iv hp₁
  rw [pin₁.reg .rbx (by decide), iv₁] at iv₂
  have stash₂ := call_stash hp₁ h₂
  simp only [pin₁.reg .rdx (by decide)] at stash₂
  have stash₂' := stash₂.trans stash₁
  change WP isa (.block (([.mov .rax (.mem (memOp .rsi 0)), .alu .xor .rax (.mem (memOp .rbx 0)),
    .store (memOp .rsi 0) .rax] : List Instr) ++
    ([.mov .rax (.mem (memOp .rdx 256)), .store (memOp .rbx 0) .rax] : List Instr))) s₂ _
  rw [WP.block_append_iff]
  obtain ⟨s₃, run₃, keep₃⟩ := xor64_ok s₂ .rsi .rbx (by decide) (by decide)
    hp₂.readData hp₂.readIv hp₂.writeData
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have frame₃ : Frame [dataR s₂] s₂.mem s₃.mem := by
    rw [keep₃.mem]; exact frame_store64 _ _ _
  have pin₃ := Pinned.of_keep keep₃ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  have pin₀₃ := pin₂.trans pin₃
  have hp₃ := pin₀₃.pre hp
  have data₃ : Spec.Rc2.blockAt s₃.mem (s.gpr .rsi) =
      Spec.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi))
        (Spec.Rc2.blockAt s.mem (s.gpr .rsi))) (Spec.Rc2.blockAt s.mem (s.gpr .rbx)) := by
    have h : Spec.Rc2.blockAt s₃.mem (s₂.gpr .rsi) =
        Spec.Rc2.xorBlock (Spec.Rc2.blockAt s₂.mem (s₂.gpr .rsi)) (Spec.Rc2.blockAt s₂.mem (s₂.gpr .rbx)) := by
      rw [keep₃.mem]; exact blockAt_xor _ _ _
    rw [pin₂.reg .rsi (by decide), pin₂.reg .rbx (by decide), output₂, iv₂] at h
    exact h
  have stash₃ := blockAt_frame frame₃ (stashR s₂).base
    (by simpa using (hp₂.dataBuf.sub_right (stash_sub s₂)).symm)
  simp only [pin₂.reg .rdx (by decide)] at stash₃
  have stash₃' := stash₃.trans stash₂'
  obtain ⟨s₄, run₄, keep₄⟩ := copy64_ok s₃ .rdx .rbx 256 0 (by decide)
    (hp₃.readBuf 256 (by decide)) (by simpa using hp₃.writeIv)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  simp only [BitVec.add_zero] at keep₄
  have frame₄ : Frame [ivR s₃] s₃.mem s₄.mem := by
    rw [keep₄.mem]; exact frame_store64 _ _ _
  have pin₄ := Pinned.of_keep keep₄ ((frame_store64 _ _ _).mono (by simp [stepWrites]))
  refine ⟨pin₀₃.trans pin₄, ?_, ?_⟩
  · have same := blockAt_frame frame₄ (s₃.gpr .rsi) (by simpa using hp₃.ivData.symm)
    rw [pin₀₃.reg .rsi (by decide)] at same
    exact same.trans data₃
  · have out : Spec.Rc2.blockAt s₄.mem (s₃.gpr .rbx) = Spec.Rc2.blockAt s₃.mem (stashR s₃).base := by
      rw [keep₄.mem]; exact blockAt_copy _ _ _
    simp only [pin₀₃.reg .rbx (by decide), pin₀₃.reg .rdx (by decide)] at out
    exact out.trans stash₃'

end VG.Proof.Rc2.X86_64.Cbc
