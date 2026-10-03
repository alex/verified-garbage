import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Argon2.AArch64.FillWritePrefix
import VerifiedGarbage.Proof.Argon2.AArch64.CountCandidates

/-! Merged from `Proof.Argon2.AArch64.FillWrite`. -/
section
/-! Whole-block first-pass copying and later-pass XOR, with a frame proof. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillWrite

theorem code_ok (s : State)
    (hs : (⟨s.gpr .x1, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (hw : (⟨s.gpr .x0, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa code s fun t =>
      blockAt t.mem (s.gpr .x0) =
        (if s.gpr .x5 = 0 then blockAt s.mem (s.gpr .x1)
          else xorBlock (blockAt s.mem (s.gpr .x1)) (blockAt s.mem (s.gpr .x0))) ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.sp = s.sp := by
  unfold code
  refine WP.seq ((CountCandidates.compare_ok s).mono ?_)
  rintro a ⟨flag, ka⟩
  have src : a.gpr .x1 = s.gpr .x1 := ka.regs .x1 (by simp)
  have dest : a.gpr .x0 = s.gpr .x0 := ka.regs .x0 (by simp)
  have hs' : (⟨a.gpr .x1, 1024⟩ : Region) ∈ a.rd ++ a.wr := by
    rw [src, ka.rd, ka.wr]; exact hs
  have hw' : (⟨a.gpr .x0, 1024⟩ : Region) ∈ a.wr := by
    rw [dest, ka.wr]; exact hw
  have hd' : (⟨a.gpr .x1, 1024⟩ : Region).Disjoint ⟨a.gpr .x0, 1024⟩ := by
    rw [src, dest]; exact hd
  refine WP.ite (decide (s.gpr .x5 = 0)) (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, flag, Bool.beq_eq_decide_eq]) ?_ ?_
  · intro h
    have zero := of_decide_eq_true h
    refine (prefix_ok false 128 (by decide) a hs' hw' hd').mono ?_
    rintro t ⟨written, frame, keeps, mx⟩
    refine ⟨?_, ?_, ?_, mx.trans ka.sp⟩
    · rw [dest] at written
      rw [ite_eq_left zero, written_block written]
      simp only [result, Bool.false_eq_true, ite_false, ka.mem, src]
    · rw [dest, ka.mem] at frame; exact frame
    · exact (show CopyKeeps s a from ⟨fun r _ h13 h14 h15 => ka.regs r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h13, h14, h15⟩), ka.rd, ka.wr⟩).trans keeps
  · intro h
    have nonzero := of_decide_eq_false h
    refine (prefix_ok true 128 (by decide) a hs' hw' hd').mono ?_
    rintro t ⟨written, frame, keeps, mx⟩
    refine ⟨?_, ?_, ?_, mx.trans ka.sp⟩
    · rw [dest] at written
      rw [ite_eq_right nonzero, written_block written]
      simp only [result, ite_true, ka.mem, src]
    · rw [dest, ka.mem] at frame; exact frame
    · exact (show CopyKeeps s a from ⟨fun r _ h13 h14 h15 => ka.regs r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h13, h14, h15⟩), ka.rd, ka.wr⟩).trans keeps

end VG.Proof.Argon2.AArch64.FillWrite
end

/-! Use block writes in a matrix allocation with larger permission regions. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillWrite

theorem code_cover_ok (s : State)
    (hs : Covers [⟨s.gpr .x1, 1024⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨s.gpr .x0, 1024⟩] s.wr)
    (hd : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa code s fun t =>
      blockAt t.mem (s.gpr .x0) =
        (if s.gpr .x5 = 0 then blockAt s.mem (s.gpr .x1)
          else xorBlock (blockAt s.mem (s.gpr .x1)) (blockAt s.mem (s.gpr .x0))) ∧
      Frame [⟨s.gpr .x0, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.sp = s.sp := by
  let a := s.withRegions [⟨s.gpr .x1, 1024⟩] [⟨s.gpr .x0, 1024⟩]
  obtain ⟨tr, t, he, value, frame, keeps, mx⟩ := code_ok a (by simp [a]) (by simp [a]) hd
  have cover : Covers (a.rd ++ a.wr) (s.rd ++ s.wr) := by
    intro p n ⟨r, hr, hc⟩
    change r ∈ [⟨s.gpr .x1, 1024⟩, ⟨s.gpr .x0, 1024⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs p n ⟨_, by simp, hc⟩
    · obtain ⟨r, hr, hc⟩ := hw p n ⟨_, by simp, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  have he' := Exec.widen (rd := s.rd) (wr := s.wr) he cover hw
  simp only [a, State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨tr, t.withRegions s.rd s.wr, he', value, frame, ?_, mx⟩
  exact ⟨keeps.1, rfl, rfl⟩

end VG.Proof.Argon2.AArch64.FillWrite
