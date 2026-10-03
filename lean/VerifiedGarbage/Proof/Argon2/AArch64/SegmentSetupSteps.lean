import VerifiedGarbage.Impl.Argon2.AArch64.SegmentSetup
import VerifiedGarbage.Proof.Argon2.AArch64.FillSegment

/-! Merged from `Proof.Argon2.AArch64.FillContext`. -/
section
/-! A segment context allows its starting and final indices, including an empty suffix. -/

namespace VG.Proof.Argon2.AArch64.FillContext

open VG VG.AArch64 VG.Spec.Argon2

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
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

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
  have bp := k.regs .x19 (by decide)
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [k.mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [k.mem, bp]
  refine ⟨h.parameters, h.layout.of_preserved bp (k.sp) base work k.rd k.wr,
    h.cache.of_keeps k, ?_, h.position.of_keeps k, ?_⟩
  · rw [base, work]; exact h.matrixWork
  · rw [k.mem, bp]; exact h.lanesWord

theorem finished_context {p : Params} {pass lane slice : Nat} {s t : State} {state : FillState}
    (parameters : Parameters p pass lane slice) (h : FillSegment.Finished s t p pass lane slice state) :
    ∃ old, Ready p pass lane slice p.segmentLen old t := by
  obtain ⟨old, cache⟩ := h.cache
  exact ⟨old, parameters, h.layout, cache, h.matrixWork, h.position, h.lanesWord⟩

end VG.Proof.Argon2.AArch64.FillContext
end

/-! Select index two only in slice zero of pass zero. -/

namespace VG.Proof.Argon2.AArch64.SegmentSetup

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.SegmentSetup

def start (pass slice : Nat) : Nat := if pass = 0 ∧ slice = 0 then 2 else 0

theorem start_active (pass slice : Nat) : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ start pass slice := by
  unfold start; split <;> omega

theorem start_le (pass slice : Nat) (g : Nat) (minimum : 2 ≤ g) : start pass slice ≤ g := by
  unfold start; split <;> omega

theorem first_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa (.block first) s fun t =>
      eval (.zero .x .x15) t = some (decide (s.mem.readW (off (s.gpr .x19) 0) 64 = 0#64 ∧ s.gpr .x22 = 0#64)) ∧
      Divide.Keeps [.x3, .x13, .x14, .x15] s t := by
  simp only [off, BitVec.add_zero] at hr
  apply WP.of_runBlock
  simp only [first, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.logic, Impl.Argon2.AArch64.Instructions.mark,
    Impl.Argon2.AArch64.Instructions.mov, Impl.Argon2.AArch64.Instructions.comparei,
    Impl.Argon2.AArch64.Instructions.compare, Impl.Argon2.AArch64.Instructions.imm,
    show 0 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, addr, State.load, Size.bytes, Size.bits,
    show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide, hr, and_self,
    show 0 < 4096 from by decide, Nat.reduceMul, Nat.reduceLT,
    show (63 : Nat) < 64 from by decide, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, BitVec.setWidth_eq, BitVec.add_zero,
    Bool.toNat_true, sub_value, show (0#16).setWidth 64 = 0#64 from rfl,
    BitVec.sub_zero, reduceCtorEq, ite_true, ite_false,
    eval, Bool.beq_eq_decide_eq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', off]
  refine ⟨?_, ?_⟩
  · congr 1
    exact propext BitVec.or_eq_zero_iff
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    all_goals rfl

theorem register_ok (s : State) (register : Reg) (value : Nat) (bound : value < 65536) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.imm register value].flatten) s fun t =>
      t.gpr register = BitVec.ofNat 64 value ∧ Divide.Keeps [register] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Instructions.imm, bound, ite_true,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits, Nat.reduceMul,
    Nat.reduceLT, BitVec.shiftLeft_zero, RegUpd.gpr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · change (BitVec.ofNat 16 value).setWidth 64 = BitVec.ofNat 64 value
    exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) bound
  · constructor
    · intro r hr
      simp only [List.mem_singleton] at hr
      simp only [RegUpd.gpr_write, hr, ite_false]
    all_goals rfl

theorem index_ok (s : State) (pass slice : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8)
    (passWord : s.mem.readW (off (s.gpr .x19) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .x22 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) : WP isa index s fun t =>
      t.gpr .x23 = BitVec.ofNat 64 (start pass slice) ∧ Divide.Keeps [.x3, .x23, .x13, .x14, .x15] s t := by
  unfold index
  refine WP.seq ((first_ok s hr).mono ?_)
  rintro a ⟨flag, keeps⟩
  have firstFlag : eval (.zero .x .x15) a = some (decide (pass = 0 ∧ slice = 0)) := by
    rw [flag, passWord, sliceWord]
    have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 := ReferenceMap.word_zero pass passBound
    have sliceZero : BitVec.ofNat 64 slice = 0#64 ↔ slice = 0 := ReferenceMap.word_zero slice sliceBound
    simp only [passZero, sliceZero]
  refine WP.ite (decide (pass = 0 ∧ slice = 0)) firstFlag ?_ ?_
  · intro mode
    refine (register_ok a .x23 2 (by decide)).mono ?_
    rintro t ⟨value, changed⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
    unfold start; simp only [of_decide_eq_true mode]; exact value
  · intro mode
    refine (register_ok a .x23 0 (by decide)).mono ?_
    rintro t ⟨value, changed⟩
    refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
    unfold start; simp only [of_decide_eq_false mode, ite_false]; exact value

theorem check_ok (s : State)
    (ha : (s.gpr .x23).toNat < 2 ^ 63) (hb : (s.gpr .x21).toNat < 2 ^ 63) :
    WP isa (.block check) s fun t =>
      eval (.nonzero .x .x14) t = some (decide ((s.gpr .x23).toNat < (s.gpr .x21).toNat)) ∧
      Divide.Keeps [.x14, .x15] s t := by
  simp only [check, List.flatten_cons, List.flatten_nil, List.append_nil]
  refine (Instructions.compare_ok s .x23 .x21 ha hb).mono ?_
  rintro t ⟨value, keeps⟩
  refine ⟨?_, keeps⟩
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, value]
  cases decide ((s.gpr .x23).toNat < (s.gpr .x21).toNat) <;> rfl

end VG.Proof.Argon2.AArch64.SegmentSetup
