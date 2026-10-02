import VerifiedGarbage.Proof.Argon2.X86_64.RandomSourcePrepare

/-! The cell update does not disturb the cached independent-address block. -/

namespace VG.Proof.Argon2.X86_64.RandomSource

open VG VG.X86_64 VG.Spec.Argon2

theorem Ready.after_fill {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : Ready p pass lane slice index old s) (done : FillKernel.Done s t p pass lane slice index) :
    Ready p pass lane slice index old t := by
  have bp := done.regs .rbp (by simp [calleeSaved])
  have sp := done.regs .rsp (by simp [calleeSaved])
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word h.filling 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := done.frame_word h.filling 248 (by decide) (by decide)
  refine ⟨done.retains h.filling, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, h.cache.bound, ?_⟩
    · constructor
      · rw [done.rd, done.wr, bp]; exact h.cache.layout.frameRead
      · rw [done.wr, work]; exact h.cache.layout.workWrite
      · rw [bp, work]; exact h.cache.layout.frameWork
      · rw [bp, sp]; exact h.cache.layout.frameStack
      · rw [sp, work]; exact h.cache.layout.stackWork
    · rw [done.rd, done.wr, bp]; exact h.cache.reads
    · rw [done.wr, bp]; exact h.cache.write
    · exact ⟨(done.frame_word h.filling 0 (by decide) (by decide)).trans h.cache.words.passWord,
        (done.regs .rbx (by simp [calleeSaved])).trans h.cache.words.laneWord,
        (done.regs .r14 (by simp [calleeSaved])).trans h.cache.words.sliceWord,
        (done.frame_word h.filling 240 (by decide) (by decide)).trans h.cache.words.blocksWord,
        (done.frame_word h.filling 72 (by decide) (by decide)).trans h.cache.words.passesWord,
        (done.frame_word h.filling 112 (by decide) (by decide)).trans h.cache.words.variantWord,
        (done.frame_word h.filling 8 (by decide) (by decide)).trans h.cache.words.counterWord⟩
    · rcases h.cache.cached with zero | cached
      · exact Or.inl zero
      · apply Or.inr
        rw [work]
        have kept : blockAt t.mem (off (AddressCalls.work s) 6144) =
            blockAt s.mem (off (AddressCalls.work s) 6144) := by
          apply FillCompress.block_frame done.frame
          intro r hr
          simp only [FillKernel.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
          have cacheSub : Region.Sub ⟨off (AddressCalls.work s) 6144, 1024⟩ ⟨AddressCalls.work s, 8192⟩ :=
            Offset.sub_base _ (by decide)
          rcases hr with rfl | rfl | rfl | rfl
          · exact (h.matrixWork.symm.sub_left cacheSub).sub_right
              (FillKernel.cell_sub p _ h.filling.bounds.lanesPositive h.filling.bounds.laneBound
                (Proof.Argon2.column_lt p h.filling.bounds.lanesPositive
                  h.filling.bounds.sliceBound h.filling.bounds.indexBound))
          · exact Offset.disjoint_base (AddressCalls.work s) (d := 6144) (n := 1024) (k := 5120)
              (by decide) (by decide)
          · exact h.cache.layout.stackWork.symm.sub_left cacheSub
          · exact (h.cache.layout.frameWork.symm.sub_left cacheSub).sub_right
              (Offset.sub_base _ (by decide))
        exact kept.trans cached
  · rw [base, work]; exact h.matrixWork

end VG.Proof.Argon2.X86_64.RandomSource
