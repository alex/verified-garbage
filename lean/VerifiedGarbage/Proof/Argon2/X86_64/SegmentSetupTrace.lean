import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetupPrepare
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! Cache reset and initial-index selection branch only on public parameters. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

structure RelatedReady (p : Params) (pass lane slice : Nat) (s t : State) : Prop where
  left : Ready p pass lane slice s
  right : Ready p pass lane slice t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t

theorem RelatedReady.of_keeps {p : Params} {pass lane slice : Nat} {s t a b : State}
    (h : RelatedReady p pass lane slice s t)
    (ka : Divide.Keeps [.rax, .rcx, .r15] s a) (kb : Divide.Keeps [.rax, .rcx, .r15] t b) :
    RelatedReady p pass lane slice a b := by
  have protectedRegs : ∀ r ∈ [Reg.rbp, .rsp, .rbx, .r12, .r13, .r14], r ∉ [Reg.rax, .rcx, .r15] := by decide
  refine ⟨h.left.of_state (fun r hr => ka.regs r (protectedRegs r hr)) ka.mem ka.rd ka.wr,
    h.right.of_state (fun r hr => kb.regs r (protectedRegs r hr)) kb.mem kb.rd kb.wr, ?_, ?_, ?_, ?_⟩
  · rw [ka.regs .rbp (by decide), kb.regs .rbp (by decide)]; exact h.bases
  · rw [ka.regs .rsp (by decide), kb.regs .rsp (by decide)]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .rbp (by decide), kb.regs .rbp (by decide)]
    exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .rbp (by decide), kb.regs .rbp (by decide)]
    exact h.work

theorem reset_trace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp) reset (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem reset_public_rel (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) reset (RelatedReady p pass lane slice) := by
  have trace := reset_trace.mono (P' := RelatedReady p pass lane slice)
    (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨reset_ok s p pass lane slice h.left, reset_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨ha.ready, hb.ready, ?_, ?_, ha.matrix.trans (hp.matrices.trans hb.matrix.symm),
    ha.work.trans (hp.work.trans hb.work.symm)⟩
  · rw [ha.regs .rbp (by simp [calleeSaved]), hb.regs .rbp (by simp [calleeSaved])]; exact hp.bases
  · rw [ha.regs .rsp (by simp [calleeSaved]), hb.regs .rsp (by simp [calleeSaved])]; exact hp.stacks

theorem first_spec_ok (s : State) (p : Params) (pass lane slice : Nat) (h : Ready p pass lane slice s) :
    WP isa (.block first) s fun t => t.zf = decide (pass = 0 ∧ slice = 0) ∧ Divide.Keeps [.rcx] s t := by
  obtain ⟨old, words⟩ := h.words
  refine (first_ok s (h.reads 0 (by simp))).mono ?_
  rintro t ⟨flag, keeps⟩
  refine ⟨?_, keeps⟩
  rw [flag, words.passWord, words.sliceWord]
  have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 :=
    ReferenceMap.word_zero pass (Nat.lt_trans h.parameters.passBound (by decide))
  have sliceZero : BitVec.ofNat 64 slice = 0#64 ↔ slice = 0 :=
    ReferenceMap.word_zero slice (Nat.lt_trans h.parameters.sliceBound (by decide))
  simp only [passZero, sliceZero]

theorem first_trace : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp) (.block first) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem first_public_rel (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) (.block first)
      (fun s t => RelatedReady p pass lane slice s t ∧ s.zf = t.zf) := by
  have trace := first_trace.mono (P' := RelatedReady p pass lane slice)
    (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨first_spec_ok s p pass lane slice h.left, first_spec_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps (ka.mono (by decide)) (kb.mono (by decide)), fa.trans fb.symm⟩

theorem index_trace (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) index (fun _ _ => True) := by
  have two : RelCT isa (fun _ _ : State => True) (.block [.mov .r15 (.imm 2)]) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)
  have zero : RelCT isa (fun _ _ : State => True) (.block [.mov .r15 (.imm 0)]) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)
  have branches : RelCT isa (fun s t => RelatedReady p pass lane slice s t ∧ s.zf = t.zf)
      (.ite .e (.block [.mov .r15 (.imm 2)]) (.block [.mov .r15 (.imm 0)])) (fun _ _ => True) :=
    RelCT.ite (by intro s t h; simp only [eval, h.2])
      (two.mono (fun _ _ _ => trivial) (fun _ _ h => h))
      (zero.mono (fun _ _ _ => trivial) (fun _ _ h => h))
  exact (first_public_rel p pass lane slice).seq branches

theorem prepare_trace (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) prepare (fun _ _ => True) :=
  (reset_public_rel p pass lane slice).seq (index_trace p pass lane slice)

end VG.Proof.Argon2.X86_64.SegmentSetup
