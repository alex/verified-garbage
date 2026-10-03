import VerifiedGarbage.Impl.Argon2.AArch64.RandomSource
import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelStable
import VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheSelect
import VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheWord
import VerifiedGarbage.Proof.Argon2.AArch64.AddressModeSteps
import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceMapState
import VerifiedGarbage.Proof.Argon2.AArch64.FillKernel

/-! Merged from `Proof.Argon2.AArch64.FillKernelInvariant`. -/
section
/-! Each active-cell update retains the frame and matrix allocation invariant. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem Done.frame_word {s t : State} {p : Params} {pass lane slice index : Nat}
    (h : Ready p pass lane slice index s) (done : Done s t p pass lane slice index)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 16 ∨ 24 ≤ d) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs])]
  have sub : Region.Sub ⟨off (s.gpr .x19) d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  have currentSub : Region.Sub ⟨current s p lane slice index, 1024⟩ ⟨matrix s, p.blocks * 1024⟩ :=
    cell_sub p _ h.bounds.lanesPositive h.bounds.laneBound
      (Proof.Argon2.column_lt p h.bounds.lanesPositive h.bounds.sliceBound h.bounds.indexBound)
  exact done.frame.readW (r := ⟨off (s.gpr .x19) d, 8⟩) (Region.contains_self _ _) (by
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
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs])
  have sp := done.sp
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
  · exact ⟨(done.regs .x24 (by simp [FillCompress.loopRegs])).trans h.position.current,
      (done.regs .x20 (by simp [FillCompress.loopRegs])).trans h.position.laneLength,
      (done.regs .x21 (by simp [FillCompress.loopRegs])).trans h.position.segmentLength,
      (done.regs .x22 (by simp [FillCompress.loopRegs])).trans h.position.slice,
      (done.regs .x23 (by simp [FillCompress.loopRegs])).trans h.position.index⟩

end VG.Proof.Argon2.AArch64.FillKernel
end

/-! Merged from `Proof.Argon2.AArch64.AddressMode`. -/
section
/-! The segment mode is exactly the reviewed Argon2d/i/id addressing predicate. -/

namespace VG.Proof.Argon2.AArch64.AddressMode

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressMode

def value (s : State) : Addr :=
  let kind := s.mem.readW (off (s.gpr .x19) 112) 64
  let pass := s.mem.readW (off (s.gpr .x19) 0) 64
  (Divide.mask (decide (kind = 1)) ||| ((Divide.mask (decide (kind = 2)) &&&
    Divide.mask (decide (pass = 0#64))) &&& Divide.mask (decide ((s.gpr .x22).toNat < 2)))) &&& 1

def changed : List Reg := [.x8, .x4, .x5, .x6, .x7, .x12, .x13, .x14, .x15]

theorem code_ok (s : State)
    (kindRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 112) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa code s fun t => t.gpr .x6 = value s ∧ Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((kind_ok s kindRead).mono ?_)
  rintro a ⟨i, id, ka⟩
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 0) 8 := by
    rw [ka.rd, ka.wr, ka.regs .x19 (by decide)]; exact passRead
  refine WP.seq ((pass_ok a read).mono ?_)
  rintro b ⟨zero, kb⟩
  refine (slice_ok b).mono ?_
  rintro t ⟨result, kt⟩
  refine ⟨?_, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩
  rw [result, kb.regs .x6 (by decide), i, kb.regs .x4 (by decide), id, zero,
    ka.mem, ka.regs .x19 (by decide), kb.regs .x22 (by decide), ka.regs .x22 (by decide)]
  rfl

theorem masks : ∀ a b c d : Bool,
    (Divide.mask a ||| ((Divide.mask b &&& Divide.mask c) &&& Divide.mask d)) &&& 1 =
      (BitVec.ofBool (a || (b && c && d))).setWidth 64 := by decide +kernel

theorem variants : ∀ v : Spec.Argon2.Variant, ∀ a b : Bool,
    (decide (BitVec.ofNat 64 v.code = (1 : Addr)) ||
      (decide (BitVec.ofNat 64 v.code = (2 : Addr)) && a && b)) =
    ((v == .i) || ((v == .id) && a && b)) := by
  intro v
  cases v <;> decide +kernel

theorem value_spec (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (kindWord : s.mem.readW (off (s.gpr .x19) 112) 64 = BitVec.ofNat 64 p.variant.code)
    (passWord : s.mem.readW (off (s.gpr .x19) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .x22 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) :
    value s = (BitVec.ofBool (Spec.Argon2.independent p pass slice)).setWidth 64 := by
  have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 := ReferenceMap.word_zero pass passBound
  unfold value
  rw [kindWord, passWord, sliceWord, masks,
    ReferenceMap.word_nat slice sliceBound]
  simp only [passZero]
  unfold Spec.Argon2.independent
  rw [variants, Bool.beq_eq_decide_eq pass 0]

theorem code_spec_ok (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (kindRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 112) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8)
    (kindWord : s.mem.readW (off (s.gpr .x19) 112) 64 = BitVec.ofNat 64 p.variant.code)
    (passWord : s.mem.readW (off (s.gpr .x19) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .x22 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) :
    WP isa code s fun t => t.gpr .x6 =
      (BitVec.ofBool (Spec.Argon2.independent p pass slice)).setWidth 64 ∧ Divide.Keeps changed s t :=
  (code_ok s kindRead passRead).mono (fun _ h =>
    ⟨h.1.trans (value_spec s p pass slice kindWord passWord sliceWord passBound sliceBound), h.2⟩)

end VG.Proof.Argon2.AArch64.AddressMode
end

/-! Merged from `Proof.Argon2.AArch64.AddressCacheState`. -/
section
/-! Merged from `Proof.Argon2.AArch64.AddressCache`. -/
section
/-! Complete cached random-word selection against RFC 9106's address block. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCache

structure Done (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  selected : Selected s t p pass lane slice
  random : t.gpr .x0 =
    (addressBlock p pass lane slice (wanted s))[(s.gpr .x23).toNat % 128]'(Nat.mod_lt _ (by decide))

theorem code_ok (p : Params) (pass lane slice old : Nat) (s : State)
    (h : Ready p pass lane slice old s) :
    WP isa code s (Done s · p pass lane slice) := by
  unfold code
  refine WP.seq ((selected_ok p pass lane slice old s h).mono ?_)
  intro a selected
  refine (word_ok a selected.layout).mono ?_
  rintro t ⟨random, keeps⟩
  have regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r := by
    intro r hr
    have ne : r ∉ [Reg.x3, .x8, .x0, .x12, .x13, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (keeps.regs r ne).trans (selected.regs r hr)
  have bp := keeps.regs .x19 (by decide)
  have sp := keeps.sp
  have work' : AddressCalls.work t = AddressCalls.work a := by
    unfold AddressCalls.work; rw [bp, keeps.mem]
  have layout : AddressCalls.Ready t := by
    constructor
    · rw [keeps.rd, keeps.wr, bp]; exact selected.layout.frameRead
    · rw [work', keeps.wr]; exact selected.layout.workWrite
    · rw [bp, work']; exact selected.layout.frameWork
    · rw [bp, sp]; exact selected.layout.frameStack
    · rw [sp, work']; exact selected.layout.stackWork
  refine ⟨⟨?_, layout, work'.trans selected.work_eq, regs,
    keeps.rd.trans selected.rd, keeps.wr.trans selected.wr, ?_,
    keeps.sp.trans selected.sp, ?_⟩, ?_⟩
  · rw [keeps.mem]; exact selected.block
  · rw [keeps.mem]; exact selected.frame
  · rw [bp, keeps.mem]; exact selected.counterWord
  · rw [selected.work_eq, selected.regs .x23 (by simp [FillCompress.loopRegs]), selected.block] at random
    exact random

end VG.Proof.Argon2.AArch64.AddressCache
end

/-! Retain the filling header and allocation across independent-address regeneration. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2

theorem Selected.frame_word {s t : State} {p : Params} {pass lane slice : Nat}
    (layout : AddressCalls.Ready s) (h : Selected s t p pass lane slice)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 8 ∨ 16 ≤ d) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [h.regs .x19 (by simp [FillCompress.loopRegs])]
  have sub : Region.Sub ⟨off (s.gpr .x19) d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  exact h.frame.readW (r := ⟨off (s.gpr .x19) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact layout.frameWork.sub_left sub
    · exact layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega) (by decide)) (by decide)

theorem Selected.words {s t : State} {p : Params} {pass lane slice old : Nat}
    (ready : Ready p pass lane slice old s) (h : Selected s t p pass lane slice) :
    AddressHeader.Words p pass lane slice (wanted s) t := by
  exact ⟨(h.frame_word ready.layout 0 (by decide) (by decide)).trans ready.words.passWord,
    (h.regs .x24 (by simp [FillCompress.loopRegs])).trans ready.words.laneWord,
    (h.regs .x22 (by simp [FillCompress.loopRegs])).trans ready.words.sliceWord,
    (h.frame_word ready.layout 240 (by decide) (by decide)).trans ready.words.blocksWord,
    (h.frame_word ready.layout 72 (by decide) (by decide)).trans ready.words.passesWord,
    (h.frame_word ready.layout 112 (by decide) (by decide)).trans ready.words.variantWord,
    h.counterWord.trans (counter_nat _)⟩

theorem Ready.of_keeps {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : Ready p pass lane slice old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    Ready p pass lane slice old t := by
  have regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r := by
    intro r hr
    apply k.regs
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have stable := AddressCalls.stable_of_frame h.layout regs k.rd k.wr
    (by rw [k.mem]; exact Frame.refl _ _) k.sp
  refine ⟨stable.ready, stable.reads h.reads, ?_, stable.words h.layout h.words, ?_⟩
  · rw [k.wr, k.regs .x19 (by decide)]; exact h.write
  · intro same
    have wanted' : wanted t = wanted s := by unfold wanted; rw [k.regs .x23 (by decide)]
    rw [k.mem, k.regs .x19 (by decide), k.regs .x23 (by decide)] at same
    rw [k.mem, stable.work_eq, wanted']
    exact h.cached same

end VG.Proof.Argon2.AArch64.AddressCache
end

/-! Merged from `Proof.Argon2.AArch64.AddressCacheMatrix`. -/
section
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
end

/-! Merged from `Proof.Argon2.AArch64.AddressCacheInvariant`. -/
section
/-! Cache validity does not depend on the current index, so advancing an index
retains it. Counter zero requires no cached contents; every other counter
identifies its specified independent-address block.
-/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2

structure Invariant (p : Params) (pass lane slice old : Nat) (s : State) : Prop where
  layout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  write : InRegions s.wr (off (s.gpr .x19) 8) 8
  words : AddressHeader.Words p pass lane slice old s
  bound : old < 2 ^ 64
  cached : old = 0 ∨ blockAt s.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice old

theorem wanted_bound (s : State) : wanted s < 2 ^ 64 := by
  unfold wanted
  have := (s.gpr .x23).isLt
  omega

theorem Invariant.ready {p : Params} {pass lane slice old : Nat} {s : State}
    (h : Invariant p pass lane slice old s) : Ready p pass lane slice old s := by
  refine ⟨h.layout, h.reads, h.write, h.words, ?_⟩
  intro same
  have word : BitVec.ofNat 64 (wanted s) = BitVec.ofNat 64 old := by
    unfold wanted
    rw [← counter_nat]; exact same.trans h.words.counterWord
  have equal := (ReferenceMap.word_eq _ _ (wanted_bound s) h.bound).mp word
  rcases h.cached with zero | cached
  · exfalso
    exact counter_ne_zero _ (same.trans (h.words.counterWord.trans (by rw [zero]; rfl)))
  · rw [← equal] at cached
    exact cached

theorem Selected.invariant {s t : State} {p : Params} {pass lane slice old : Nat}
    (ready : Ready p pass lane slice old s) (h : Selected s t p pass lane slice) :
    Invariant p pass lane slice (wanted s) t := by
  have bp := h.regs .x19 (by simp [FillCompress.loopRegs])
  refine ⟨h.layout, ?_, ?_, h.words ready, wanted_bound s, Or.inr ?_⟩
  · rw [h.rd, h.wr, bp]; exact ready.reads
  · rw [h.wr, bp]; exact ready.write
  · rw [h.work_eq]; exact h.block

theorem Invariant.zero {p : Params} {pass lane slice : Nat} {s : State}
    (h : Ready p pass lane slice 0 s) : Invariant p pass lane slice 0 s :=
  ⟨h.layout, h.reads, h.write, h.words, by decide, Or.inl rfl⟩

theorem Invariant.of_state {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : Invariant p pass lane slice old s)
    (regs : ∀ r ∈ [Reg.x19, .x24, .x22], t.gpr r = s.gpr r)
    (sp : t.sp = s.sp) (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    Invariant p pass lane slice old t := by
  have bp := regs .x19 (by simp)
  have work : AddressCalls.work t = AddressCalls.work s := by
    unfold AddressCalls.work; rw [mem, bp]
  refine ⟨?_, ?_, ?_, ?_, h.bound, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.layout.frameRead
    · rw [wr, work]; exact h.layout.workWrite
    · rw [bp, work]; exact h.layout.frameWork
    · rw [bp, sp]; exact h.layout.frameStack
    · rw [sp, work]; exact h.layout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.write
  · exact ⟨by rw [mem, bp]; exact h.words.passWord,
      (regs .x24 (by simp)).trans h.words.laneWord,
      (regs .x22 (by simp)).trans h.words.sliceWord,
      by rw [mem, bp]; exact h.words.blocksWord,
      by rw [mem, bp]; exact h.words.passesWord,
      by rw [mem, bp]; exact h.words.variantWord,
      by rw [mem, bp]; exact h.words.counterWord⟩
  · rw [mem, work]; exact h.cached

theorem Invariant.of_keeps {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : Invariant p pass lane slice old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    Invariant p pass lane slice old t := by
  apply h.of_state _ k.sp k.mem k.rd k.wr
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact k.regs _ (by decide)

end VG.Proof.Argon2.AArch64.AddressCache
end

/-! Retain the source invariants while selecting the public addressing mode. -/

namespace VG.Proof.Argon2.AArch64.RandomSource

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.RandomSource

structure Ready (p : Params) (pass lane slice index old : Nat) (s : State) : Prop where
  filling : FillKernel.Ready p pass lane slice index s
  cache : AddressCache.Invariant p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩

theorem Ready.of_keeps {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : Ready p pass lane slice index old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    Ready p pass lane slice index old t := by
  refine ⟨h.filling.of_keeps k, h.cache.of_keeps k, ?_⟩
  have matrix : FillKernel.matrix t = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [k.mem, k.regs .x19 (by decide)]
  have work : AddressCalls.work t = AddressCalls.work s := by
    unfold AddressCalls.work; rw [k.mem, k.regs .x19 (by decide)]
  rw [matrix, work]; exact h.matrixWork

theorem test_ok (s : State) : WP isa (.block test) s fun t =>
    eval (.zero .x .x15) t = some (decide (s.gpr .x6 = 0#64)) ∧
      Divide.Keeps [.x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [test, Impl.Argon2.AArch64.Instructions.comparei,
    Impl.Argon2.AArch64.Instructions.compare, Impl.Argon2.AArch64.Instructions.imm,
    show 0 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, Size.bits, Nat.reduceMul, Nat.reduceLT,
    show (63 : Nat) < 64 from by decide, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, BitVec.setWidth_eq,
    Bool.toNat_true, sub_value, show (0#16).setWidth 64 = 0#64 from rfl, BitVec.sub_zero, reduceCtorEq, ite_true, ite_false,
    eval, Bool.beq_eq_decide_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem bool_zero : ∀ b : Bool, decide ((BitVec.ofBool b).setWidth 64 = 0#64) = !b := by
  decide +kernel

theorem prepare_ok (s : State) (p : Params) (pass lane slice index old : Nat)
    (h : Ready p pass lane slice index old s) : WP isa prepare s fun t =>
      eval (.zero .x .x15) t = some (!independent p pass slice) ∧ Divide.Keeps ReferenceMap.changed s t := by
  unfold prepare
  refine WP.seq ((AddressMode.code_spec_ok s p pass slice
    (h.cache.reads 112 (by simp)) (h.cache.reads 0 (by simp))
    h.cache.words.variantWord h.filling.passWord h.filling.position.slice
    (Nat.lt_trans h.filling.bounds.passBound (by decide))
    (Nat.lt_trans h.filling.bounds.sliceBound (by decide))).mono ?_)
  rintro a ⟨mode, keeps⟩
  refine (test_ok a).mono ?_
  rintro t ⟨flag, tested⟩
  refine ⟨?_, (keeps.mono (by decide)).trans (tested.mono (by decide))⟩
  rw [flag, mode, bool_zero]

end VG.Proof.Argon2.AArch64.RandomSource
