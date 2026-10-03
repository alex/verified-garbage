import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupPrepare
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT

/-! Cache reset and initial-index selection branch only on public parameters. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

structure RelatedReady (p : Params) (pass lane slice : Nat) (s t : State) : Prop where
  left : Ready p pass lane slice s
  right : Ready p pass lane slice t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t

theorem RelatedReady.of_keeps {p : Params} {pass lane slice : Nat} {s t a b : State}
    (h : RelatedReady p pass lane slice s t)
    (ka : Divide.Keeps [.x8, .x3, .x23, .x13, .x14, .x15] s a) (kb : Divide.Keeps [.x8, .x3, .x23, .x13, .x14, .x15] t b) :
    RelatedReady p pass lane slice a b := by
  have protectedRegs : ∀ r ∈ [Reg.x19, .x24, .x20, .x21, .x22], r ∉ [Reg.x8, .x3, .x23, .x13, .x14, .x15] := by decide
  refine ⟨h.left.of_state (fun r hr => ka.regs r (protectedRegs r hr)) ka.sp ka.mem ka.rd ka.wr,
    h.right.of_state (fun r hr => kb.regs r (protectedRegs r hr)) kb.sp kb.mem kb.rd kb.wr, ?_, ?_, ?_, ?_⟩
  · rw [ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.bases
  · rw [ka.sp, kb.sp]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]
    exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]
    exact h.work

theorem reset_trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    reset (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem reset_public_rel (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) reset (RelatedReady p pass lane slice) := by
  have trace := reset_trace.mono (P' := RelatedReady p pass lane slice)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨reset_ok s p pass lane slice h.left, reset_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨ha.ready, hb.ready, ?_, ?_, ha.matrix.trans (hp.matrices.trans hb.matrix.symm),
    ha.work.trans (hp.work.trans hb.work.symm)⟩
  · rw [ha.regs .x19 (by simp [FillCompress.loopRegs]), hb.regs .x19 (by simp [FillCompress.loopRegs])]; exact hp.bases
  · rw [ha.sp, hb.sp]; exact hp.stacks

theorem first_spec_ok (s : State) (p : Params) (pass lane slice : Nat) (h : Ready p pass lane slice s) :
    WP isa (.block first) s fun t => eval (.zero .x .x15) t = some (decide (pass = 0 ∧ slice = 0)) ∧ Divide.Keeps [.x3, .x13, .x14, .x15] s t := by
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

theorem first_trace : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block first) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem first_public_rel (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) (.block first)
      (fun s t => RelatedReady p pass lane slice s t ∧ eval (.zero .x .x15) s = eval (.zero .x .x15) t) := by
  have trace := first_trace.mono (P' := RelatedReady p pass lane slice)
    (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨first_spec_ok s p pass lane slice h.left, first_spec_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps (ka.mono (by decide)) (kb.mono (by decide)), fa.trans fb.symm⟩

theorem index_trace (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) index (fun _ _ => True) := by
  have two : RelCT isa (fun s t : State => s.sp = t.sp)
      (.block [Impl.Argon2.AArch64.Instructions.imm .x23 2].flatten) (fun _ _ => True) :=
    (RelCT.taintRegs (τ := Taint.ofRegs [])
      (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
      [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  have zero : RelCT isa (fun s t : State => s.sp = t.sp)
      (.block [Impl.Argon2.AArch64.Instructions.imm .x23 0].flatten) (fun _ _ => True) :=
    (RelCT.taintRegs (τ := Taint.ofRegs [])
      (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
      [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  have branches : RelCT isa (fun s t => RelatedReady p pass lane slice s t ∧
      eval (.zero .x .x15) s = eval (.zero .x .x15) t)
      (.ite (.zero .x .x15)
        (.block [Impl.Argon2.AArch64.Instructions.imm .x23 2].flatten)
        (.block [Impl.Argon2.AArch64.Instructions.imm .x23 0].flatten)) (fun _ _ => True) :=
    RelCT.ite (by intro s t h; exact h.2)
      (two.mono (fun _ _ h => h.1.1.stacks) (fun _ _ h => h))
      (zero.mono (fun _ _ h => h.1.1.stacks) (fun _ _ h => h))
  exact (first_public_rel p pass lane slice).seq branches

theorem prepare_trace (p : Params) (pass lane slice : Nat) :
    RelCT isa (RelatedReady p pass lane slice) prepare (fun _ _ => True) :=
  (reset_public_rel p pass lane slice).seq (index_trace p pass lane slice)

end VG.Proof.Argon2.AArch64.SegmentSetup
