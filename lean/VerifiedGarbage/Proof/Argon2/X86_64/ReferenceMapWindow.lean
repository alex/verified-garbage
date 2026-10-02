import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapLane
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceStart

/-! The selected eligible window and its chronological starting column. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

structure Counted (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s t : State) : Prop where
  selected : t.gpr .rdi = BitVec.ofNat 64 (chosenLane p pass lane slice (s.gpr .rdi))
  current : t.gpr .rsi = BitVec.ofNat 64 lane
  count : t.gpr .r8 = BitVec.ofNat 64 (windowSize p pass lane slice index (s.gpr .rdi))
  start : t.gpr .r10 = BitVec.ofNat 64 (windowStart p pass slice)
  original : t.gpr .r11 = s.gpr .rdi
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
  have passB : (b.gpr .r9).toNat = pass := by
    rw [kb.regs .r9 (by decide), prepared.pass]
  have same : decide (b.gpr .rdi = b.gpr .rsi) =
      (chosenLane p pass lane slice (s.gpr .rdi) == lane) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq]
    rw [kb.regs .rdi (by decide), kb.regs .rsi (by decide), prepared.selected, prepared.current]
    exact word_eq _ _ (bounds.chosenLane_bound64 _) bounds.lane_bound64
  refine (ReferenceCount.code_nat_ok b p pass slice index passB pb.laneLength
    pb.segmentLength pb.slice pb.index bounds.segment_le_lane bounds.index_bound64
    bounds.window_positive.1 bounds.window_positive.2).mono ?_
  rintro t ⟨countWord, kt⟩
  have kt' : Divide.Keeps changed b t := kt.mono (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, pb.of_keeps kt', prepared.keeps.trans (kb'.trans kt')⟩
  · exact (kt.regs .rdi (by decide)).trans ((kb.regs .rdi (by decide)).trans prepared.selected)
  · exact (kt.regs .rsi (by decide)).trans ((kb.regs .rsi (by decide)).trans prepared.current)
  · simpa only [windowSize, same] using countWord
  · exact (kt.regs .r10 (by decide)).trans startWord
  · exact (kt.regs .r11 (by decide)).trans ((kb.regs .r11 (by decide)).trans prepared.original)

end VG.Proof.Argon2.X86_64.ReferenceMap
