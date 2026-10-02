import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapWindow
import VerifiedGarbage.Proof.Argon2.AArch64.Relative

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
