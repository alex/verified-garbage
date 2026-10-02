import VerifiedGarbage.Proof.Argon2.X86_64.FillWritePrefix
import VerifiedGarbage.Proof.Argon2.X86_64.CountCandidates

/-! Whole-block first-pass copying and later-pass XOR, with a frame proof. -/

namespace VG.Proof.Argon2.X86_64.FillWrite

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillWrite

theorem code_ok (s : State)
    (hs : (⟨s.gpr .rsi, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (hw : (⟨s.gpr .rdi, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩) :
    WP isa code s fun t =>
      blockAt t.mem (s.gpr .rdi) =
        (if s.gpr .r9 = 0 then blockAt s.mem (s.gpr .rsi)
          else xorBlock (blockAt s.mem (s.gpr .rsi)) (blockAt s.mem (s.gpr .rdi))) ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  unfold code
  refine WP.seq ((CountCandidates.compare_ok s).mono ?_)
  rintro a ⟨flag, ka⟩
  have src : a.gpr .rsi = s.gpr .rsi := ka.regs .rsi (by simp)
  have dest : a.gpr .rdi = s.gpr .rdi := ka.regs .rdi (by simp)
  have hs' : (⟨a.gpr .rsi, 1024⟩ : Region) ∈ a.rd ++ a.wr := by
    rw [src, ka.rd, ka.wr]; exact hs
  have hw' : (⟨a.gpr .rdi, 1024⟩ : Region) ∈ a.wr := by
    rw [dest, ka.wr]; exact hw
  have hd' : (⟨a.gpr .rsi, 1024⟩ : Region).Disjoint ⟨a.gpr .rdi, 1024⟩ := by
    rw [src, dest]; exact hd
  refine WP.ite (decide (s.gpr .r9 = 0)) (by simp only [eval, flag]) ?_ ?_
  · intro h
    have zero := of_decide_eq_true h
    refine (prefix_ok false 128 (by decide) a hs' hw' hd').mono ?_
    rintro t ⟨written, frame, keeps, mx⟩
    refine ⟨?_, ?_, ?_, mx.trans ka.mxcsr⟩
    · rw [dest] at written
      rw [ite_eq_left zero, written_block written]
      simp only [result, Bool.false_eq_true, ite_false, ka.mem, src]
    · rw [dest, ka.mem] at frame; exact frame
    · exact (show CopyKeeps s a from ⟨fun r _ => ka.regs r (by simp), ka.rd, ka.wr⟩).trans keeps
  · intro h
    have nonzero := of_decide_eq_false h
    refine (prefix_ok true 128 (by decide) a hs' hw' hd').mono ?_
    rintro t ⟨written, frame, keeps, mx⟩
    refine ⟨?_, ?_, ?_, mx.trans ka.mxcsr⟩
    · rw [dest] at written
      rw [ite_eq_right nonzero, written_block written]
      simp only [result, ite_true, ka.mem, src]
    · rw [dest, ka.mem] at frame; exact frame
    · exact (show CopyKeeps s a from ⟨fun r _ => ka.regs r (by simp), ka.rd, ka.wr⟩).trans keeps

end VG.Proof.Argon2.X86_64.FillWrite
