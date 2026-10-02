import VerifiedGarbage.Proof.Argon2.X86_64.FillWrite
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-! Use block writes in a matrix allocation with larger permission regions. -/

namespace VG.Proof.Argon2.X86_64.FillWrite

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillWrite

theorem code_cover_ok (s : State)
    (hs : Covers [⟨s.gpr .rsi, 1024⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (hd : (⟨s.gpr .rsi, 1024⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩) :
    WP isa code s fun t =>
      blockAt t.mem (s.gpr .rdi) =
        (if s.gpr .r9 = 0 then blockAt s.mem (s.gpr .rsi)
          else xorBlock (blockAt s.mem (s.gpr .rsi)) (blockAt s.mem (s.gpr .rdi))) ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  let a := s.withRegions [⟨s.gpr .rsi, 1024⟩] [⟨s.gpr .rdi, 1024⟩]
  obtain ⟨tr, t, he, value, frame, keeps, mx⟩ := code_ok a (by simp [a]) (by simp [a]) hd
  have cover : Covers (a.rd ++ a.wr) (s.rd ++ s.wr) := by
    intro p n ⟨r, hr, hc⟩
    change r ∈ [⟨s.gpr .rsi, 1024⟩, ⟨s.gpr .rdi, 1024⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs p n ⟨_, by simp, hc⟩
    · obtain ⟨r, hr, hc⟩ := hw p n ⟨_, by simp, hc⟩
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  have he' := Exec.widen (rd := s.rd) (wr := s.wr) he cover hw
  simp only [a, State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨tr, t.withRegions s.rd s.wr, he', value, frame, ?_, mx⟩
  exact ⟨keeps.1, rfl, rfl⟩

end VG.Proof.Argon2.X86_64.FillWrite
