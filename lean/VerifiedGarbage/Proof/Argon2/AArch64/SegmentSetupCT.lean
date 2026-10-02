import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetup
import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupTrace
import VerifiedGarbage.Proof.Argon2.AArch64.FillSegmentCT

/-! Complete segment setup and filling expose only the specified reference log. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

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
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
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
  · rw [ha.regs .x19 (by simp [FillCompress.loopRegs]) (by decide), hb.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)]
    exact hp.ready.bases
  · rw [ha.sp, hb.sp]
    exact hp.ready.stacks
  · have indices := hp.indices
    rw [Proof.Argon2.segment_start p pass lane slice leftState hp.ready.left.parameters.segment_bound.1,
      Proof.Argon2.segment_start p pass lane slice rightState hp.ready.right.parameters.segment_bound.1] at indices
    exact indices

theorem PreparedRelated.of_keeps {p : Params} {pass lane slice : Nat} {leftState rightState : FillState}
    {s t a b : State} (h : PreparedRelated p pass lane slice leftState rightState s t)
    (ka : Divide.Keeps [.x14, .x15] s a) (kb : Divide.Keeps [.x14, .x15] t b) :
    PreparedRelated p pass lane slice leftState rightState a b := by
  refine ⟨h.left.of_keeps (ka.mono (by decide)), h.right.of_keeps (kb.mono (by decide)), ?_, ?_, ?_, ?_, ?_, ?_, h.indices⟩
  · rw [ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.bases
  · rw [ka.sp, kb.sp]; exact h.stacks
  · unfold FillKernel.matrix
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.matrices
  · unfold AddressCalls.work
    rw [ka.mem, kb.mem, ka.regs .x19 (by decide), kb.regs .x19 (by decide)]; exact h.work
  · unfold FillKernel.matrix; rw [ka.mem, ka.regs .x19 (by decide)]; exact h.leftMatrix
  · unfold FillKernel.matrix; rw [kb.mem, kb.regs .x19 (by decide)]; exact h.rightMatrix

theorem check_context_ok (s : State) (p : Params) (pass lane slice : Nat)
    (h : FillContext.Ready p pass lane slice (start pass slice) 0 s) : WP isa (.block check) s fun t =>
      eval (.nonzero .x .x14) t = some (decide (start pass slice < p.segmentLen)) ∧ Divide.Keeps [.x14, .x15] s t := by
  have minimum := h.parameters.segment_bound
  have segmentBound : p.segmentLen < 2 ^ 63 := by
    have laneLe : p.laneLen ≤ p.blocks := by
      rw [Proof.Argon2.blocks_lanes p h.parameters.lanesPositive]
      exact Nat.le_mul_of_pos_left _ h.parameters.lanesPositive
    have segments := Proof.Argon2.laneLen_segments p h.parameters.lanesPositive
    have blocks := Proof.Argon2.blocks_le_memory p
    have memoryBound := h.parameters.memoryBound
    omega
  have startBound := Nat.lt_of_le_of_lt (start_le pass slice p.segmentLen minimum.1) segmentBound
  have left : (s.gpr .x23).toNat < 2 ^ 63 := by
    rw [h.position.index, ReferenceMap.word_nat _ (Nat.lt_trans startBound (by decide))]; exact startBound
  have right : (s.gpr .x21).toNat < 2 ^ 63 := by
    rw [h.position.segmentLength, ReferenceMap.word_nat _ minimum.2]; exact segmentBound
  refine (check_ok s left right).mono ?_
  rintro t ⟨flag, keeps⟩
  refine ⟨?_, keeps⟩
  rw [flag, h.position.index, h.position.segmentLength,
    ReferenceMap.word_nat (start pass slice) (Nat.lt_of_le_of_lt (start_le _ _ _ minimum.1) minimum.2),
    ReferenceMap.word_nat p.segmentLen minimum.2]

theorem check_trace : RelCT isa (fun s t : State => s.sp = t.sp)
    (.block check) (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [])
    (fun _ _ h => ⟨h, by intro r hr; simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem check_public_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (PreparedRelated p pass lane slice leftState rightState) (.block check)
      (fun s t => PreparedRelated p pass lane slice leftState rightState s t ∧
        eval (.nonzero .x .x14) s = some (decide (start pass slice < p.segmentLen)) ∧ eval (.nonzero .x .x14) t = some (decide (start pass slice < p.segmentLen))) := by
  have trace := check_trace.mono (P' := PreparedRelated p pass lane slice leftState rightState)
    (fun _ _ h => h.stacks) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => ⟨check_context_ok s p pass lane slice h.left, check_context_ok t p pass lane slice h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨fa, ka⟩, ⟨fb, kb⟩⟩ := h
  exact ⟨hp.of_keeps ka kb, fa, fb⟩

theorem code_rel (p : Params) (pass lane slice : Nat) (leftState rightState : FillState) :
    RelCT isa (Related p pass lane slice leftState rightState) code (fun _ _ => True) := by
  have branches : RelCT isa
      (fun s t => PreparedRelated p pass lane slice leftState rightState s t ∧
        eval (.nonzero .x .x14) s = some (decide (start pass slice < p.segmentLen)) ∧ eval (.nonzero .x .x14) t = some (decide (start pass slice < p.segmentLen)))
      (.ite (.nonzero .x .x14) Impl.Argon2.AArch64.FillSegment.loop (.block [])) (fun _ _ => True) := by
    refine RelCT.ite (by intro s t h; simp only [h.2.1, h.2.2]) ?_ ?_
    · intro s t ts tt a b hp ea eb
      have active : start pass slice < p.segmentLen := by
        have taken := hp.2
        simp only [hp.1.2.1, Option.some.injEq, decide_eq_true_eq] at taken
        exact taken
      have left := hp.1.1.left.activate active (start_active pass slice)
      have right := hp.1.1.right.activate active (start_active pass slice)
      have related : FillSegment.Related p pass lane slice (start pass slice)
          (p.segmentLen - start pass slice) 0 leftState rightState s t :=
        ⟨⟨left, right, hp.1.1.bases, hp.1.1.stacks, hp.1.1.matrices, hp.1.1.work⟩,
          hp.1.1.leftMatrix, hp.1.1.rightMatrix, hp.1.1.indices⟩
      exact FillSegment.loop_rel p pass lane slice (start pass slice) (p.segmentLen - start pass slice) 0
        leftState rightState (by omega) (by omega) _ _ _ _ _ _ related ea eb
    · intro s t ts tt a b hp ea eb
      cases ea with
      | block runA =>
        cases eb with
        | block runB =>
          obtain ⟨rfl, rfl⟩ := runA
          obtain ⟨rfl, rfl⟩ := runB
          exact ⟨rfl, trivial⟩
  exact (prepare_public_rel p pass lane slice leftState rightState).seq
    ((check_public_rel p pass lane slice leftState rightState).seq branches)

end VG.Proof.Argon2.AArch64.SegmentSetup
