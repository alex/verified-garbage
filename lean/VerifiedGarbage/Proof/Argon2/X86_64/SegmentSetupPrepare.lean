import VerifiedGarbage.Impl.Argon2.X86_64.SegmentSetup
import VerifiedGarbage.Proof.Argon2.X86_64.FillSegment

/-! Merged from `Proof.Argon2.X86_64.SegmentSetupSteps`. -/
section
/-! Merged from `Proof.Argon2.X86_64.FillContext`. -/
section
/-! A segment context allows its starting and final indices, including an empty suffix. -/

namespace VG.Proof.Argon2.X86_64.FillContext

open VG VG.X86_64 VG.Spec.Argon2

structure Parameters (p : Params) (pass lane slice : Nat) : Prop where
  lanesPositive : 0 < p.lanes
  lanesBound : p.lanes < 2 ^ 32
  memoryMinimum : 8 * p.lanes ≤ p.memory
  memoryBound : p.memory < 2 ^ 32
  passBound : pass < 2 ^ 32
  laneBound : lane < p.lanes
  sliceBound : slice < 4

structure Ready (p : Params) (pass lane slice index old : Nat) (s : State) : Prop where
  parameters : Parameters p pass lane slice
  layout : FillKernel.Layout p s
  cache : AddressCache.Invariant p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  position : ReferenceMap.Position p lane slice index s
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Ready.activate {p : Params} {pass lane slice index old : Nat} {s : State}
    (h : Ready p pass lane slice index old s) (bound : index < p.segmentLen)
    (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) : RandomSource.Ready p pass lane slice index old s :=
  ⟨⟨h.layout, ⟨h.parameters.lanesPositive, h.parameters.lanesBound, h.parameters.memoryMinimum,
    h.parameters.memoryBound, h.parameters.passBound, h.parameters.laneBound, h.parameters.sliceBound,
    bound, active⟩, h.position, h.cache.words.passWord, h.lanesWord⟩, h.cache, h.matrixWork⟩

theorem Parameters.segment_bound {p : Params} {pass lane slice : Nat} (h : Parameters p pass lane slice) :
    2 ≤ p.segmentLen ∧ p.segmentLen < 2 ^ 64 := by
  have minimum := Proof.Argon2.segmentLen_ge_two p h.lanesPositive h.memoryMinimum
  have le : p.segmentLen ≤ p.blocks := by
    have blocks := Proof.Argon2.blocks_lanes p h.lanesPositive
    have segments := Proof.Argon2.laneLen_segments p h.lanesPositive
    have laneLe : p.laneLen ≤ p.blocks := by rw [blocks]; exact Nat.le_mul_of_pos_left _ h.lanesPositive
    omega
  exact ⟨minimum, Nat.lt_of_le_of_lt le
    (Nat.lt_trans (Nat.lt_of_le_of_lt (Proof.Argon2.blocks_le_memory p) h.memoryBound) (by decide))⟩

theorem Ready.of_keeps {p : Params} {pass lane slice index old : Nat} {s t : State}
    (h : Ready p pass lane slice index old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    Ready p pass lane slice index old t := by
  have bp := k.regs .rbp (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  refine ⟨h.parameters, h.layout.of_preserved bp (k.regs .rsp (by decide)) base work k.rd k.wr,
    h.cache.of_keeps k, ?_, h.position.of_keeps k, ?_⟩
  · rw [base, work]; exact h.matrixWork
  · rw [k.mem, bp]; exact h.lanesWord

theorem finished_context {p : Params} {pass lane slice : Nat} {s t : State} {state : FillState}
    (parameters : Parameters p pass lane slice) (h : FillSegment.Finished s t p pass lane slice state) :
    ∃ old, Ready p pass lane slice p.segmentLen old t := by
  obtain ⟨old, cache⟩ := h.cache
  exact ⟨old, parameters, h.layout, cache, h.matrixWork, h.position, h.lanesWord⟩

end VG.Proof.Argon2.X86_64.FillContext
end

/-! Select index two only in slice zero of pass zero. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

def start (pass slice : Nat) : Nat := if pass = 0 ∧ slice = 0 then 2 else 0

theorem start_active (pass slice : Nat) : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ start pass slice := by
  unfold start; split <;> omega

theorem start_le (pass slice : Nat) (g : Nat) (minimum : 2 ≤ g) : start pass slice ≤ g := by
  unfold start; split <;> omega

theorem first_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa (.block first) s fun t =>
      t.zf = decide (s.mem.readW (off (s.gpr .rbp) 0) 64 = 0#64 ∧ s.gpr .r14 = 0#64) ∧
      Divide.Keeps [.rcx] s t := by
  apply WP.of_runBlock
  simp only [first, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags,
    reduceCtorEq, ite_true, ite_false,
    show BitVec.signExtend 64 (0 : BitVec 32) = (0 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · change ((s.mem.readW (off (s.gpr .rbp) 0) 64 ||| s.gpr .r14) - 0#64 == 0#64) = _
    rw [BitVec.sub_zero]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, BitVec.or_eq_zero_iff, decide_eq_true_eq]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
    all_goals rfl

theorem register_ok (s : State) (register : Reg) (value : BitVec 32) :
    WP isa (.block [.mov register (.imm value)]) s fun t =>
      t.gpr register = value.signExtend 64 ∧ Divide.Keeps [register] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem index_ok (s : State) (pass slice : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8)
    (passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .r14 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) : WP isa index s fun t =>
      t.gpr .r15 = BitVec.ofNat 64 (start pass slice) ∧ Divide.Keeps [.rcx, .r15] s t := by
  unfold index
  refine WP.seq ((first_ok s hr).mono ?_)
  rintro a ⟨flag, keeps⟩
  have firstFlag : a.zf = decide (pass = 0 ∧ slice = 0) := by
    rw [flag, passWord, sliceWord]
    have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 := ReferenceMap.word_zero pass passBound
    have sliceZero : BitVec.ofNat 64 slice = 0#64 ↔ slice = 0 := ReferenceMap.word_zero slice sliceBound
    simp only [passZero, sliceZero]
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) (by simp only [eval, firstFlag]) ?_ ?_
  · intro mode
    refine (register_ok a .r15 2).mono ?_
    rintro t ⟨value, changed⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
    unfold start; simp only [of_decide_eq_true mode]; exact value
  · intro mode
    refine (register_ok a .r15 0).mono ?_
    rintro t ⟨value, changed⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
    unfold start; simp only [of_decide_eq_false mode, ite_false]; exact value

theorem check_ok (s : State) : WP isa (.block check) s fun t =>
    t.cf = decide ((s.gpr .r15).toNat < (s.gpr .r13).toNat) ∧ Divide.Keeps [] s t := by
  apply WP.of_runBlock
  simp only [check, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.cf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r _; exact congrFun (RegUpd.gpr_arithFlags _ _ _ _) r
  all_goals rfl

end VG.Proof.Argon2.X86_64.SegmentSetup
end

/-! Merged from `Proof.Argon2.X86_64.SegmentSetupReset`. -/
section
/-! Merged from `Proof.Argon2.X86_64.SegmentSetupReady`. -/
section
/-! Segment setup needs no previously valid cached block. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (pass lane slice : Nat) (s : State) : Prop where
  parameters : FillContext.Parameters p pass lane slice
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  write : InRegions s.wr (off (s.gpr .rbp) 8) 8
  words : ∃ old, AddressHeader.Words p pass lane slice old s
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  laneLength : s.gpr .r12 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Ready.of_state {p : Params} {pass lane slice : Nat} {s t : State}
    (h : Ready p pass lane slice s)
    (regs : ∀ r ∈ [Reg.rbp, .rsp, .rbx, .r12, .r13, .r14], t.gpr r = s.gpr r)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Ready p pass lane slice t := by
  have bp := regs .rbp (by simp)
  have sp := regs .rsp (by simp)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.parameters, h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_,
    (regs .r12 (by simp)).trans h.laneLength, (regs .r13 (by simp)).trans h.segmentLength, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.addressLayout.frameRead
    · rw [wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    refine ⟨old, ?_, (regs .rbx (by simp)).trans words.laneWord,
      (regs .r14 (by simp)).trans words.sliceWord, ?_, ?_, ?_, ?_⟩
    all_goals rw [mem, bp]
    · exact words.passWord
    · exact words.blocksWord
    · exact words.passesWord
    · exact words.variantWord
    · exact words.counterWord
  · rw [base, work]; exact h.matrixWork
  · rw [mem, bp]; exact h.lanesWord

theorem Ready.saved {p : Params} {pass lane slice : Nat} {s t : State}
    (h : Ready p pass lane slice s) (saved : AddressCache.Saved s t) : Ready p pass lane slice t := by
  have bp := congrFun saved.regs Reg.rbp
  have sp := congrFun saved.regs Reg.rsp
  have base : FillKernel.matrix t = FillKernel.matrix s := saved.read 232 (by decide) (by decide)
  refine ⟨h.parameters, h.layout.of_preserved bp sp base saved.work_eq saved.rd saved.wr,
    saved.ready, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [saved.rd, saved.wr, bp]; exact h.reads
  · rw [saved.wr, bp]; exact h.write
  · obtain ⟨old, words⟩ := h.words
    exact ⟨(s.gpr .rax).toNat, saved.words words (by simp)⟩
  · rw [base, saved.work_eq]; exact h.matrixWork
  · rw [saved.regs]; exact h.laneLength
  · rw [saved.regs]; exact h.segmentLength
  · exact (saved.read 184 (by decide) (by decide)).trans h.lanesWord

end VG.Proof.Argon2.X86_64.SegmentSetup
end

/-! Reset the counter while preserving the segment header and matrix allocation. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

structure Reset (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  ready : Ready p pass lane slice t
  words : AddressHeader.Words p pass lane slice 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (s.gpr .rbp) 8, 8⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem reset_ok (s : State) (p : Params) (pass lane slice : Nat) (h : Ready p pass lane slice s) :
    WP isa reset s (Reset s · p pass lane slice) := by
  unfold reset
  refine WP.seq ((register_ok s .rax 0).mono ?_)
  rintro a ⟨value, keeps⟩
  have next := h.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.mem keeps.rd keeps.wr
  refine (AddressCache.save_ready a next.addressLayout next.write).mono ?_
  intro t saved
  obtain ⟨old, words⟩ := next.words
  have matrixA : FillKernel.matrix a = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .rbp (by decide)]
  have workA : AddressCalls.work a = AddressCalls.work s := by
    unfold AddressCalls.work; rw [keeps.mem, keeps.regs .rbp (by decide)]
  refine ⟨next.saved saved, saved.words words value,
    (saved.read 232 (by decide) (by decide)).trans matrixA, saved.work_eq.trans workA,
    ?_, saved.rd.trans keeps.rd, saved.wr.trans keeps.wr, ?_, saved.mxcsr.trans keeps.mxcsr⟩
  · intro r hr
    have ne : r ∉ [Reg.rax] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (congrFun saved.regs r).trans (keeps.regs r ne)
  · have frame := saved.frame
    rw [keeps.mem, keeps.regs .rbp (by decide)] at frame
    exact frame

end VG.Proof.Argon2.X86_64.SegmentSetup
end

/-! The prepared context covers ordinary and empty first-segment suffixes. -/

namespace VG.Proof.Argon2.X86_64.SegmentSetup

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.SegmentSetup

structure Prepared (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  context : FillContext.Ready p pass lane slice (start pass slice) 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ calleeSaved, r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨off (s.gpr .rbp) 8, 8⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem prepare_ok (s : State) (p : Params) (pass lane slice : Nat) (h : Ready p pass lane slice s) :
    WP isa prepare s (Prepared s · p pass lane slice) := by
  unfold prepare
  refine WP.seq ((reset_ok s p pass lane slice h).mono ?_)
  intro a reset
  refine (index_ok a pass slice (reset.ready.reads 0 (by simp)) reset.words.passWord reset.words.sliceWord
    (Nat.lt_trans h.parameters.passBound (by decide))
    (Nat.lt_trans h.parameters.sliceBound (by decide))).mono ?_
  rintro t ⟨value, keeps⟩
  have core := reset.ready.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.mem keeps.rd keeps.wr
  have cacheA : AddressCache.Invariant p pass lane slice 0 a :=
    ⟨reset.ready.addressLayout, reset.ready.reads, reset.ready.write, reset.words, by decide, Or.inl rfl⟩
  have cache := cacheA.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact keeps.regs _ (by decide)) keeps.mem keeps.rd keeps.wr
  have base : FillKernel.matrix t = FillKernel.matrix a := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.regs .rbp (by decide)]
  have work : AddressCalls.work t = AddressCalls.work a := by
    unfold AddressCalls.work; rw [keeps.mem, keeps.regs .rbp (by decide)]
  refine ⟨⟨core.parameters, core.layout, cache, core.matrixWork,
    ⟨cache.words.laneWord, core.laneLength, core.segmentLength, cache.words.sliceWord, value⟩, core.lanesWord⟩,
    base.trans reset.matrix, work.trans reset.work, ?_, keeps.rd.trans reset.rd,
    keeps.wr.trans reset.wr, ?_, keeps.mxcsr.trans reset.mxcsr⟩
  · intro r hr ne
    have outside : r ∉ [Reg.rcx, .r15] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (reset.regs r hr)
  · rw [keeps.mem]; exact reset.frame

theorem Prepared.represents {p : Params} {pass lane slice : Nat} {s t : State}
    (ready : Ready p pass lane slice s) (h : Prepared s t p pass lane slice) (blocks : Array Block)
    (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  rw [h.matrix]
  refine ⟨represented.size, ?_⟩
  intro k hk
  apply Eq.trans _ (represented.block k hk)
  apply FillCompress.block_frame h.frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact (ready.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
    (Offset.sub_base _ (by decide))

end VG.Proof.Argon2.X86_64.SegmentSetup
