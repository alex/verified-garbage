import VerifiedGarbage.Proof.Argon2.X86_64.InitFillReady

/-! Each stage writes only the matrix, hash scratch, output, call stack and local hash prefix. -/

namespace VG.Proof.Argon2.X86_64.InitFill

open VG VG.X86_64 VG.Spec.Argon2

def writes (s : State) (p : Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨FinalOutput.work s, 16384⟩,
    ⟨FinalOutput.output s, p.tagLen⟩, below (s.gpr .rsp) 24, ⟨s.gpr .rbp, 72⟩]

theorem initialization_frame {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : Frame (writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have blocks := Proof.Argon2.blocks_lanes p h.environment.parameters.lanesPositive
    exact ⟨⟨FillKernel.matrix s, p.blocks * 1024⟩, by simp [writes], by rw [blocks, Nat.mul_comm 1024]; intro _ h; exact h⟩
  · exact ⟨⟨FinalOutput.work s, 16384⟩, by simp [writes], by rw [h.scratch]; intro _ h; exact h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨⟨s.gpr .rbp, 72⟩, by simp [writes], Offset.sub_base _ (by decide)⟩

theorem setup_frame {s t : State} {p : Params} (h : Frame [⟨s.gpr .rbp, 8⟩] s.mem t.mem) :
    Frame (writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨s.gpr .rbp, 72⟩, by simp [writes], Region.sub_prefix (by decide)⟩

theorem filling_frame {s t : State} {p : Params} (positive : 0 < p.blocks) (h : Frame (FillFinish.writes s p) s.mem t.mem) :
    Frame (writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [FillFinish.writes, FillIterations.writes, Finish.writes,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨⟨FinalOutput.work s, 16384⟩, by simp [writes], Region.sub_prefix (by decide)⟩
  · exact ⟨below (s.gpr .rsp) 24, by simp [writes], below_sub (by decide) (by decide)⟩
  · exact ⟨⟨s.gpr .rbp, 72⟩, by simp [writes], Region.sub_prefix (by decide)⟩
  · exact ⟨⟨FillKernel.matrix s, p.blocks * 1024⟩, by simp [writes], Region.sub_prefix (by omega)⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩

end VG.Proof.Argon2.X86_64.InitFill
