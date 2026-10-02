import VerifiedGarbage.Proof.Argon2.AArch64.FillWritePrefix
import VerifiedGarbage.Proof.Argon2.AArch64.CountCandidates

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
