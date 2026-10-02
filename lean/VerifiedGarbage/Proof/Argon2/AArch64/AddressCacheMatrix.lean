import VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheState
import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelInvariant
import VerifiedGarbage.Proof.Argon2.Matrix

/-! Independent-address generation leaves every matrix cell intact. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2

theorem Selected.filling_ready {s t : State} {p : Params} {pass lane slice index : Nat}
    (cacheLayout : AddressCalls.Ready s) (h : FillKernel.Ready p pass lane slice index s)
    (done : Selected s t p pass lane slice) : FillKernel.Ready p pass lane slice index t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs])
  have sp := done.sp
  have matrix' : FillKernel.matrix t = FillKernel.matrix s := done.frame_word cacheLayout 232 (by decide) (by decide)
  have work' : FillKernel.work t = FillKernel.work s := done.frame_word cacheLayout 248 (by decide) (by decide)
  refine ⟨?_, h.bounds, ?_, (done.frame_word cacheLayout 0 (by decide) (by decide)).trans h.passWord,
    (done.frame_word cacheLayout 184 (by decide) (by decide)).trans h.lanesWord⟩
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
  · exact ⟨(done.regs .x24 (by simp [FillCompress.loopRegs])).trans h.position.current,
      (done.regs .x20 (by simp [FillCompress.loopRegs])).trans h.position.laneLength,
      (done.regs .x21 (by simp [FillCompress.loopRegs])).trans h.position.segmentLength,
      (done.regs .x22 (by simp [FillCompress.loopRegs])).trans h.position.slice,
      (done.regs .x23 (by simp [FillCompress.loopRegs])).trans h.position.index⟩

theorem Selected.represents {s t : State} {p : Params} {pass lane slice index : Nat}
    (cacheLayout : AddressCalls.Ready s) (h : FillKernel.Ready p pass lane slice index s)
    (matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩)
    (done : Selected s t p pass lane slice) (blocks : Array Block)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word cacheLayout 232 (by decide) (by decide)
  rw [base]
  refine ⟨represented.size, ?_⟩
  intro k hk
  have kept : blockAt t.mem (Proof.Argon2.matrixCell (FillKernel.matrix s) k) =
      blockAt s.mem (Proof.Argon2.matrixCell (FillKernel.matrix s) k) := by
    apply FillCompress.block_frame done.frame
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact matrixWork.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)
    · exact h.layout.matrixStack.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)
    · exact (h.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
        (Offset.sub_base _ (by decide))
  exact kept.trans (represented.block k hk)

end VG.Proof.Argon2.AArch64.AddressCache
