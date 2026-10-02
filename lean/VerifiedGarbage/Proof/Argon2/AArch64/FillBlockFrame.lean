import VerifiedGarbage.Proof.Argon2.AArch64.RandomSourceState

/-! Compose scratch writes with a matrix-cell write inside the derive allocation. -/

namespace VG.Proof.Argon2.AArch64.FillBlock

open VG VG.AArch64 VG.Spec.Argon2

def writes (s : State) (p : Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨AddressCalls.work s, 8192⟩,
    below s.sp 8, ⟨off (s.gpr .x19) 8, 16⟩]

theorem source_frame {s t : State} {p : Params} {pass lane slice index : Nat} {state : FillState}
    (done : RandomSource.Done s t p pass lane slice index state) : Frame (writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [RandomSource.writes, AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨⟨off (s.gpr .x19) 8, 16⟩, by simp [writes], Region.sub_prefix (by decide)⟩

theorem kernel_frame {s t : State} {p : Params} {pass lane slice index : Nat}
    (ready : FillKernel.Ready p pass lane slice index s) (done : FillKernel.Done s t p pass lane slice index) :
    Frame (writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [FillKernel.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [writes], FillKernel.cell_sub p _ ready.bounds.lanesPositive ready.bounds.laneBound
      (Proof.Argon2.column_lt p ready.bounds.lanesPositive ready.bounds.sliceBound ready.bounds.indexBound)⟩
  · exact ⟨⟨AddressCalls.work s, 8192⟩, by simp [writes], Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], Offset.sub _ (d := 16) (n := 8) (e := 8) (k := 16)
      (by decide) (by decide)⟩

end VG.Proof.Argon2.AArch64.FillBlock
