import VerifiedGarbage.Impl.Argon2.AArch64.FillBlock
import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelSpec
import VerifiedGarbage.Proof.Argon2.AArch64.RandomSourcePrepare
import VerifiedGarbage.Proof.Argon2.AArch64.RandomSource

/-! Merged from `Proof.Argon2.AArch64.RandomSourceState`. -/
section
/-! Frame words and public allocation pointers survive random-word dispatch. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2

theorem Done.frame_word {s t : State} {p : Params} {pass lane slice index old : Nat} {state : FillState}
    (h : Ready p pass lane slice index old s) (done : Done s t p pass lane slice index state)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 8 ∨ 16 ≤ d) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs])]
  have sub : Region.Sub ⟨off (s.gpr .x19) d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨off (s.gpr .x19) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [writes, AddressCache.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.cache.layout.frameWork.sub_left sub
    · exact h.cache.layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.AArch64.RandomSource
end

/-! Merged from `Proof.Argon2.AArch64.FillCacheInvariant`. -/
section
/-! The cell update does not disturb the cached independent-address block. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2

theorem Ready.after_fill {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : Ready p pass lane slice index old s) (done : FillKernel.Done s t p pass lane slice index) :
    Ready p pass lane slice index old t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs])
  have sp := done.sp
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
        (done.regs .x24 (by simp [FillCompress.loopRegs])).trans h.cache.words.laneWord,
        (done.regs .x22 (by simp [FillCompress.loopRegs])).trans h.cache.words.sliceWord,
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

end VG.Proof.Argon2.AArch64.RandomSource
end

/-! Merged from `Proof.Argon2.AArch64.FillBlockFrame`. -/
section
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
end

/-! Complete active filling cell against the reviewed matrix transition. -/

namespace VG.Proof.Argon2.AArch64.FillBlock

open VG VG.AArch64 VG.Spec.Argon2

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) (state : FillState) : Prop where
  ready : ∃ old, RandomSource.Ready p pass lane slice index old t
  represented : Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
    (fillBlock p pass slice lane index state).memory
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  sp : t.sp = s.sp

theorem code_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : RandomSource.Ready p pass lane slice index old s) (state : FillState)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks state.memory) :
    WP isa Impl.Argon2.AArch64.FillBlock.code s (Done s · p pass lane slice index state) := by
  unfold Impl.Argon2.AArch64.FillBlock.code
  refine WP.seq ((RandomSource.code_ok s p pass lane slice index old h state represented).mono ?_)
  intro a source
  obtain ⟨counter, ready⟩ := source.ready
  have baseA : FillKernel.matrix a = FillKernel.matrix s := source.frame_word h 232 (by decide) (by decide)
  have workA : AddressCalls.work a = AddressCalls.work s := source.frame_word h 248 (by decide) (by decide)
  refine (FillKernel.code_spec_ok a p pass lane slice index ready.filling state source.represented source.random).mono ?_
  rintro t ⟨done, matrix⟩
  have baseT : FillKernel.matrix t = FillKernel.matrix a := done.frame_word ready.filling 232 (by decide) (by decide)
  have workT : AddressCalls.work t = AddressCalls.work a := done.frame_word ready.filling 248 (by decide) (by decide)
  refine ⟨⟨counter, ready.after_fill done⟩, ?_, baseT.trans baseA, workT.trans workA, ?_,
    done.rd.trans source.rd, done.wr.trans source.wr, ?_, done.sp.trans source.sp⟩
  · rw [baseT]; exact matrix
  · intro r hr; exact (done.regs r hr).trans (source.regs r hr)
  · have frame := kernel_frame ready.filling done
    rw [writes, baseA, workA, source.sp,
      source.regs .x19 (by simp [FillCompress.loopRegs])] at frame
    exact (source_frame source).trans frame

end VG.Proof.Argon2.AArch64.FillBlock
