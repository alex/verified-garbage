import VerifiedGarbage.Impl.Argon2.X86_64.ReduceBlock
import VerifiedGarbage.Proof.Argon2.X86_64.FillWriteCover
import VerifiedGarbage.Proof.Argon2.FinalReduction

/-! Reuse the verified word loop with allocation-level permissions. -/

namespace VG.Proof.Argon2.X86_64.ReduceBlock

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.ReduceBlock

theorem code_ok (s : State)
    (read : Covers [⟨s.gpr .rsi, 1024⟩] (s.rd ++ s.wr))
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (separate : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩) :
    WP isa code s fun t =>
      blockAt t.mem (s.gpr .rdi) = xorBlock (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi)) ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  let a := s.withRegions [⟨s.gpr .rsi, 1024⟩] [⟨s.gpr .rdi, 1024⟩]
  obtain ⟨trace, t, run, written, frame, keeps, mx⟩ :=
    FillWrite.prefix_ok true 128 (by decide) a (by simp [a]) (by simp [a]) separate
  have cover : Covers (a.rd ++ a.wr) (s.rd ++ s.wr) := by
    intro q n ⟨r, hr, hc⟩
    change r ∈ [⟨s.gpr .rsi, 1024⟩, ⟨s.gpr .rdi, 1024⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact read q n ⟨_, by simp, hc⟩
    · obtain ⟨r, hr, hc⟩ := write q n ⟨_, by simp, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  have run' := Exec.widen (rd := s.rd) (wr := s.wr) run cover write
  simp only [a, State.withRegions_withRegions, State.withRegions_self] at run'
  refine ⟨trace, t.withRegions s.rd s.wr, run', ?_, frame, ⟨keeps.1, rfl, rfl⟩, mx⟩
  exact (written_block written).trans (Proof.Argon2.xorBlock_comm _ _)

end VG.Proof.Argon2.X86_64.ReduceBlock
