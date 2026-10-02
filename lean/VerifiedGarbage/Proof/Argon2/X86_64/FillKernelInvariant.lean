import VerifiedGarbage.Proof.Argon2.X86_64.FillKernel

/-! Each active-cell update retains the frame and matrix allocation invariant. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

theorem Done.frame_word {s t : State} {p : Params} {pass lane slice index : Nat}
    (h : Ready p pass lane slice index s) (done : Done s t p pass lane slice index)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 16 ∨ 24 ≤ d) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [done.regs .rbp (by simp [calleeSaved])]
  have sub : Region.Sub ⟨off (s.gpr .rbp) d, 8⟩ ⟨s.gpr .rbp, 272⟩ := Offset.sub_base _ bound
  have currentSub : Region.Sub ⟨current s p lane slice index, 1024⟩ ⟨matrix s, p.blocks * 1024⟩ :=
    cell_sub p _ h.bounds.lanesPositive h.bounds.laneBound
      (Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound)
  exact done.frame.readW (r := ⟨off (s.gpr .rbp) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ((h.layout.matrixFrame.sub_left currentSub).symm).sub_left sub
    · exact h.layout.frameWork.sub_left sub
    · exact h.layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega) (by decide)) (by decide)

theorem Done.retains {s t : State} {p : Params} {pass lane slice index : Nat}
    (h : Ready p pass lane slice index s) (done : Done s t p pass lane slice index) :
    Ready p pass lane slice index t := by
  have bp := done.regs .rbp (by simp [calleeSaved])
  have sp := done.regs .rsp (by simp [calleeSaved])
  have matrix' : matrix t = matrix s := done.frame_word h 232 (by decide) (by decide)
  have work' : work t = work s := done.frame_word h 248 (by decide) (by decide)
  refine ⟨?_, h.bounds, ?_, (done.frame_word h 0 (by decide) (by decide)).trans h.passWord,
    (done.frame_word h 184 (by decide) (by decide)).trans h.lanesWord⟩
  · constructor
    · rw [done.rd, done.wr, bp]; exact h.layout.frameRead
    · rw [done.wr, bp]; exact h.layout.frameWrite
    · rw [matrix', done.wr]; exact h.layout.matrixWrite
    · rw [work', done.wr]; exact h.layout.workWrite
    · rw [matrix', work']; exact h.layout.matrixWork
    · rw [matrix', bp]; exact h.layout.matrixFrame
    · rw [matrix', sp]; exact h.layout.matrixStack
    · rw [bp, work']; exact h.layout.frameWork
    · rw [bp, sp]; exact h.layout.frameStack
    · rw [sp, work']; exact h.layout.stackWork
  · exact ⟨(done.regs .rbx (by simp [calleeSaved])).trans h.position.current,
      (done.regs .r12 (by simp [calleeSaved])).trans h.position.laneLength,
      (done.regs .r13 (by simp [calleeSaved])).trans h.position.segmentLength,
      (done.regs .r14 (by simp [calleeSaved])).trans h.position.slice,
      (done.regs .r15 (by simp [calleeSaved])).trans h.position.index⟩

end VG.Proof.Argon2.X86_64.FillKernel
