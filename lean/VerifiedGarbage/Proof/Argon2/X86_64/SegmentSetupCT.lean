import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetup
import VerifiedGarbage.Proof.Argon2.X86_64.SegmentSetupTrace
import VerifiedGarbage.Proof.Argon2.X86_64.FillSegmentCT

/-! Complete segment setup and filling expose only the specified reference log. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

structure Related (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) (s t : State) : Prop where
  ready : RelatedReady p pass lane slice s t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.segment p pass lane slice 0 p.segmentLen leftState).indices =
    (Proof.Argon2.segment p pass lane slice 0 p.segmentLen rightState).indices

structure PreparedRelated (p : Params) (pass lane slice : Nat) (leftState rightState : FillState)
    (s t : State) : Prop where
  left : FillContext.Ready p pass lane slice (start pass slice) 0 s
  right : FillContext.Ready p pass lane slice (start pass slice) 0 t
  bases : s.gpr .rbp = t.gpr .rbp
  stacks : s.gpr .rsp = t.gpr .rsp
  matrices : FillKernel.matrix s = FillKernel.matrix t
  work : AddressCalls.work s = AddressCalls.work t
  leftMatrix : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks leftState.memory
  rightMatrix : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks rightState.memory
  indices : (Proof.Argon2.segment p pass lane slice (start pass slice) (p.segmentLen - start pass slice) leftState).indices =
    (Proof.Argon2.segment p pass lane slice (start pass slice) (p.segmentLen - start pass slice) rightState).indices

theorem prepare_public_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass lane slice leftState rightState) prepare
      (PreparedRelated p pass lane slice leftState rightState) := by
  have trace := (prepare_trace p pass lane slice).mono
    (P' := Related p pass lane slice leftState rightState) (fun _ _ h => h.ready) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨prepare_ok s p pass lane slice h.ready.left, prepare_ok t p pass lane slice h.ready.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨ha.context, hb.context, ?_, ?_, ha.matrix.trans (hp.ready.matrices.trans hb.matrix.symm),
    ha.work.trans (hp.ready.work.trans hb.work.symm), ha.represents hp.ready.left leftState.memory hp.leftMatrix,
    hb.represents hp.ready.right rightState.memory hp.rightMatrix, ?_⟩
  · rw [ha.regs .rbp (by simp [calleeSaved]) (by decide), hb.regs .rbp (by simp [calleeSaved]) (by decide)]
    exact hp.ready.bases
  · rw [ha.regs .rsp (by simp [calleeSaved]) (by decide), hb.regs .rsp (by simp [calleeSaved]) (by decide)]
    exact hp.ready.stacks
  · have indices := hp.indices
    rw [Proof.Argon2.segment_start p pass lane slice leftState hp.ready.left.parameters.segment_bound.1,
      Proof.Argon2.segment_start p pass lane slice rightState hp.ready.right.parameters.segment_bound.1] at indices
    exact indices

theorem PreparedRelated.of_keeps {p : Params} {pass lane slice : Nat} {leftState rightState : FillState}
    {s t a b : State} (h : PreparedRelated p pass lane slice leftState rightState s t)
    (ka : Divide.Keeps [] s a) (kb : Divide.Keeps [] t b) :
    PreparedRelated p pass lane slice leftState rightState a b := by
  refine ⟨h.left.of_keeps (ka.mono (by decide)), h.right.of_keeps (kb.mono (by decide)), ?_, ?_, ?_, ?_, ?_, ?_, h.indices⟩
  · rw [ka.regs .rbp (by simp), kb.regs .rbp (by simp)]; exact h.bases
  · rw [ka.regs .rsp (by simp), kb.regs .rsp (by simp)]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .rbp (by simp), kb.regs .rbp (by simp)]; exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .rbp (by simp), kb.regs .rbp (by simp)]; exact h.work
  · unfold FillKernel.matrix; rw [ka.mem, ka.regs .rbp (by simp)]; exact h.leftMatrix
  · unfold FillKernel.matrix; rw [kb.mem, kb.regs .rbp (by simp)]; exact h.rightMatrix

theorem check_context_ok (s : State) (p : Params) (pass lane slice : Nat)
    (h : FillContext.Ready p pass lane slice (start pass slice) 0 s) : WP isa (.block check) s fun t =>
      t.cf = decide (start pass slice < p.segmentLen) ∧ Divide.Keeps [] s t := by
  refine (check_ok s).mono ?_
  rintro t ⟨flag, keeps⟩
  have minimum := h.parameters.segment_bound
  refine ⟨?_, keeps⟩
  rw [flag, h.position.index, h.position.segmentLength,
    ReferenceMap.word_nat (start pass slice) (Nat.lt_of_le_of_lt (start_le _ _ _ minimum.1) minimum.2),
    ReferenceMap.word_nat p.segmentLen minimum.2]

theorem check_trace : RelCT isa (fun _ _ : State => True) (.block check) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)

theorem check_public_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (PreparedRelated p pass lane slice leftState rightState) (.block check)
      (fun s t => PreparedRelated p pass lane slice leftState rightState s t ∧
        s.cf = decide (start pass slice < p.segmentLen) ∧ t.cf = decide (start pass slice < p.segmentLen)) := by
  have trace := check_trace.mono (P' := PreparedRelated p pass lane slice leftState rightState)
    (fun _ _ _ => trivial) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨check_context_ok s p pass lane slice h.left, check_context_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps ka kb, fa, fb⟩

theorem code_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass lane slice leftState rightState) code (fun _ _ => True) := by
  have branches : RelCT isa
      (fun s t => PreparedRelated p pass lane slice leftState rightState s t ∧
        s.cf = decide (start pass slice < p.segmentLen) ∧ t.cf = decide (start pass slice < p.segmentLen))
      (.ite .b Impl.Argon2.X86_64.FillSegment.loop (.block [])) (fun _ _ => True) := by
    refine RelCT.ite (by intro s t h; simp only [eval, h.2.1, h.2.2]) ?_ ?_
    · intro s t ts tt a b hp ea eb
      have active : start pass slice < p.segmentLen := by
        have taken := hp.2
        simp only [eval, hp.1.2.1, Option.some.injEq, decide_eq_true_eq] at taken
        exact taken
      have left := hp.1.1.left.activate active (start_active pass slice)
      have right := hp.1.1.right.activate active (start_active pass slice)
      have related : FillSegment.Related p pass lane slice (start pass slice)
          (p.segmentLen - start pass slice) 0 leftState rightState s t :=
        ⟨⟨left, right, hp.1.1.bases, hp.1.1.stacks, hp.1.1.matrices, hp.1.1.work⟩,
          hp.1.1.leftMatrix, hp.1.1.rightMatrix, hp.1.1.indices⟩
      exact FillSegment.loop_rel p pass lane slice (start pass slice) (p.segmentLen - start pass slice) 0
        leftState rightState (by omega) (by omega) _ _ _ _ _ _ related ea eb
    · have noop : RelCT isa (fun _ _ : State => True) (.block []) (fun _ _ => True) :=
        RelCT.taint (A := taint) (Taint.ofRegs [])
          (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)
      exact noop.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  exact (prepare_public_rel p pass lane slice leftState rightState).seq
    ((check_public_rel p pass lane slice leftState rightState).seq branches)

end VG.Proof.Argon2.X86_64.SegmentSetup
