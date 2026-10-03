import VerifiedGarbage.Proof.Argon2.AArch64.Wrap
import VerifiedGarbage.Proof.Argon2.AArch64.Relative
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapLane
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceStart

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapWindow`. -/
section
/-! The selected eligible window and its chronological starting column. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

structure Counted (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x0 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .x0))
  current : t.gpr .x1 = BitVec.ofNat 64 lane
  count : t.gpr .x4 = BitVec.ofNat 64 (windowSize p pass lane slice index (s.gpr .x0))
  start : t.gpr .x6 = BitVec.ofNat 64 (windowStart p pass slice)
  original : t.gpr .x7 = s.gpr .x0
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem window_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : Bounds p pass lane slice index) (prepared : Prepared p pass lane slice index s a) :
    WP isa window a (Counted p pass lane slice index s) := by
  have segmentPositive : 0 < p.segmentLen :=
    Nat.lt_of_lt_of_le (by decide : 0 < 2)
      (Proof.Argon2.segmentLen_ge_two p bounds.lanesPositive bounds.memoryMinimum)
  unfold window
  refine WP.seq ((ReferenceStart.code_nat_ok a p pass slice bounds.lanesPositive
    segmentPositive bounds.sliceBound prepared.pass prepared.position.slice
    prepared.position.segmentLength).mono ?_)
  rintro b ⟨startWord, kb⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have pb := prepared.position.of_keeps kb'
  have passB : (b.gpr .x5).toNat = pass := by
    rw [kb.regs .x5 (by decide), prepared.pass]
  have same : decide (b.gpr .x0 = b.gpr .x1) =
      (chosenLane p pass lane slice (s.gpr .x0) == lane) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq]
    rw [kb.regs .x0 (by decide), kb.regs .x1 (by decide), prepared.selected, prepared.current]
    exact word_eq _ _ (bounds.chosenLane_bound64 _) bounds.lane_bound64
  refine (ReferenceCount.code_nat_ok b p pass slice index passB pb.laneLength
    pb.segmentLength pb.slice pb.index bounds.segment_le_lane bounds.index_bound64
    bounds.window_positive.1 bounds.window_positive.2).mono ?_
  rintro t ⟨countWord, kt⟩
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, pb.of_keeps kt', prepared.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .x0 (by decide)).trans ((kb.regs .x0 (by decide)).trans prepared.selected)
  · exact (kt.regs .x1 (by decide)).trans ((kb.regs .x1 (by decide)).trans prepared.current)
  · simpa only [windowSize, same] using countWord
  · exact (kt.regs .x6 (by decide)).trans startWord
  · exact (kt.regs .x7 (by decide)).trans ((kb.regs .x7 (by decide)).trans prepared.original)

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapRelative`. -/
section
/-! Apply the squared J₁ mapping while retaining the lane and window start. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

theorem relativeWord_ok (s : State) (positive : 0 < (s.gpr .x1).toNat)
    (bound : (s.gpr .x1).toNat < 2 ^ 32) :
    WP isa VG.Impl.Argon2.AArch64.Relative.code s fun t =>
      t.gpr .x8 = BitVec.ofNat 64
        ((s.gpr .x1).toNat - 1 - (s.gpr .x1).toNat *
          ((s.gpr .x0 &&& 0xffffffff).toNat * (s.gpr .x0 &&& 0xffffffff).toNat / 2 ^ 32) /
          2 ^ 32) ∧ Divide.Keeps [.x8, .x2, .x3, .x12, .x15] s t := by
  obtain ⟨tr, t, he, out, other, mem, rd, wr⟩ := Relative.code_nat_ok s positive bound
  refine ⟨tr, t, he, out, ?_⟩
  refine ⟨?_, mem, rd, wr, VG.AArch64.Exec.sp he⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact other r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2

structure Mapped (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x5 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .x0))
  relative : t.gpr .x8 = BitVec.ofNat 64 (relativeValue p pass lane slice index (s.gpr .x0))
  start : t.gpr .x6 = BitVec.ofNat 64 (windowStart p pass slice)
  original : t.gpr .x7 = s.gpr .x0
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem relative_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : Bounds p pass lane slice index) (counted : Counted p pass lane slice index s a) :
    WP isa relative a (Mapped p pass lane slice index s) := by
  unfold relative
  refine WP.seq ((relativeArgs_ok a).mono ?_)
  rintro b ⟨selected, random, count, kb⟩
  have countNat : (b.gpr .x1).toNat = windowSize p pass lane slice index (s.gpr .x0) := by
    rw [count, counted.count, word_nat _ (Nat.lt_trans (bounds.windowSize_bound32 _) (by decide))]
  have randomWord : b.gpr .x0 = s.gpr .x0 := random.trans counted.original
  refine (relativeWord_ok b
    (by rw [countNat]; exact bounds.windowSize_positive _)
    (by rw [countNat]; exact bounds.windowSize_bound32 _)).mono ?_
  rintro t ⟨out, kt⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, counted.position.of_keeps (kb'.trans kt'),
    counted.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .x5 (by decide)).trans (selected.trans counted.selected)
  · simpa only [relativeValue, countNat, randomWord] using out
  · exact (kt.regs .x6 (by decide)).trans ((kb.regs .x6 (by decide)).trans counted.start)
  · exact (kt.regs .x7 (by decide)).trans ((kb.regs .x7 (by decide)).trans counted.original)

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Merged from `Proof.Argon2.AArch64.ReferenceMapFinish`. -/
section
/-! Wrap the selected relative position into the lane's columns. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

structure Result (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .x5 = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .x0))
  column : t.gpr .x0 = BitVec.ofNat 64
    ((windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .x0)) % p.laneLen)
  original : t.gpr .x7 = s.gpr .x0
  position : Position p lane slice index t
  keeps : Divide.Keeps changed s t

theorem finish_ok (s a : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (bounds : Bounds p pass lane slice index) (mapped : Mapped p pass lane slice index s a) :
    WP isa finish a (Result p pass lane slice index s) := by
  unfold finish
  refine WP.seq ((wrapArgs_ok a).mono ?_)
  rintro b ⟨sum, length, kb⟩
  have sumWord : b.gpr .x0 = BitVec.ofNat 64
      (windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .x0)) := by
    rw [sum, mapped.relative, mapped.start, ← BitVec.ofNat_add, Nat.add_comm]
  have sumBound : windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .x0)
      < 2 ^ 64 := by
    have small := bounds.sum_bound (s.gpr .x0)
    have q := bounds.laneLength_bound
    omega
  have sumNat : (b.gpr .x0).toNat =
      windowStart p pass slice + relativeValue p pass lane slice index (s.gpr .x0) := by
    rw [sumWord, word_nat _ sumBound]
  have lengthNat : (b.gpr .x1).toNat = p.laneLen := by
    rw [length, mapped.position.laneLength,
      word_nat _ (Nat.lt_trans bounds.laneLength_bound (by decide))]
  refine (Wrap.code_nat_ok b (by rw [sumNat, lengthNat]; exact bounds.sum_bound _)).mono ?_
  rintro t ⟨out, kt⟩
  have kb' : Divide.Keeps changed a b := kb.mono (by decide)
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, mapped.position.of_keeps (kb'.trans kt'),
    mapped.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .x5 (by decide)).trans ((kb.regs .x5 (by decide)).trans mapped.selected)
  · rw [out, sumNat, lengthNat]
  · exact (kt.regs .x7 (by decide)).trans ((kb.regs .x7 (by decide)).trans mapped.original)

end VG.Proof.Argon2.AArch64.ReferenceMap
end

/-! Complete reference mapping against the reviewed RFC specification. -/

namespace VG.Proof.Argon2.AArch64.ReferenceMap

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReferenceMap

theorem code_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa code s (Result p pass lane slice index s) := by
  unfold code
  refine WP.seq ((prepareLanes_ok s p pass lane slice index ready).mono ?_)
  intro a ha
  refine WP.seq ((window_ok s a p pass lane slice index ready.bounds ha).mono ?_)
  intro b hb
  refine WP.seq ((relative_ok s b p pass lane slice index ready.bounds hb).mono ?_)
  intro c hc
  exact finish_ok s c p pass lane slice index ready.bounds hc

theorem spec_lane (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) :
    (Spec.Argon2.reference p pass lane slice index random).1 = chosenLane p pass lane slice random := rfl

theorem spec_column (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) :
    (Spec.Argon2.reference p pass lane slice index random).2 =
      (windowStart p pass slice + relativeValue p pass lane slice index random) % p.laneLen := rfl

theorem code_spec_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa code s fun t =>
      t.gpr .x5 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .x0)).1 ∧
      t.gpr .x0 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .x0)).2 ∧
      t.gpr .x7 = s.gpr .x0 ∧ Divide.Keeps changed s t := by
  refine (code_ok s p pass lane slice index ready).mono ?_
  intro t h
  rw [spec_lane, spec_column]
  exact ⟨h.selected, h.column, h.original, h.keeps⟩

end VG.Proof.Argon2.AArch64.ReferenceMap
