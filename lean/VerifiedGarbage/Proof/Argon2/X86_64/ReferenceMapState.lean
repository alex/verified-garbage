import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceCount
import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceMap
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapArgs`. -/
section
/-! Register preparation for the reference-index stages. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

theorem pass_ea (s : State) : s.ea { base := .rbp } = s.gpr .rbp := by
  change s.gpr .rbp + 0#64 = s.gpr .rbp
  exact BitVec.add_zero _

theorem loadPass_ok (s : State) (read : InRegions (s.rd ++ s.wr) (s.gpr .rbp) 8) :
    WP isa (.block loadPass) s fun t =>
      t.gpr .r9 = s.mem.readW (s.gpr .rbp) 64 ∧ Divide.Keeps [.r9] s t := by
  apply WP.of_runBlock
  simp only [loadPass, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    pass_ea, State.load64, read, ite_true, Option.map_some, RegUpd.gpr_setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem laneArgs_ok (s : State) : WP isa (.block laneArgs) s fun t =>
    t.gpr .rdi = s.gpr .r8 ∧ t.gpr .rsi = s.gpr .rbx ∧
    Divide.Keeps [.rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [laneArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

theorem relativeArgs_ok (s : State) : WP isa (.block relativeArgs) s fun t =>
    t.gpr .r9 = s.gpr .rdi ∧ t.gpr .rdi = s.gpr .r11 ∧ t.gpr .rsi = s.gpr .r8 ∧
    Divide.Keeps [.r9, .rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [relativeArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem wrapArgs_ok (s : State) : WP isa (.block wrapArgs) s fun t =>
    t.gpr .rdi = s.gpr .rax + s.gpr .r10 ∧ t.gpr .rsi = s.gpr .r12 ∧
    Divide.Keeps [.rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [wrapArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.ReferenceMap
end

/-! Parameters and register invariants for the complete reference mapping. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64

/-- Every stage preserves the enclosing loop's callee-saved registers. -/
def changed : List Reg := [.rax, .rdx, .rcx, .r8, .r9, .r10, .r11, .rdi, .rsi]

structure Bounds (p : Spec.Argon2.Params) (pass lane slice index : Nat) : Prop where
  lanesPositive : 0 < p.lanes
  lanesBound : p.lanes < 2 ^ 32
  memoryMinimum : 8 * p.lanes ≤ p.memory
  memoryBound : p.memory < 2 ^ 32
  passBound : pass < 2 ^ 32
  laneBound : lane < p.lanes
  sliceBound : slice < 4
  indexBound : index < p.segmentLen
  active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index

structure Position (p : Spec.Argon2.Params) (lane slice index : Nat) (s : State) : Prop where
  current : s.gpr .rbx = BitVec.ofNat 64 lane
  laneLength : s.gpr .r12 = BitVec.ofNat 64 p.laneLen
  segmentLength : s.gpr .r13 = BitVec.ofNat 64 p.segmentLen
  slice : s.gpr .r14 = BitVec.ofNat 64 slice
  index : s.gpr .r15 = BitVec.ofNat 64 index

theorem Position.of_keeps {s t : State} {p : Spec.Argon2.Params} {lane slice index : Nat}
    (h : Position p lane slice index s) (k : Divide.Keeps changed s t) :
    Position p lane slice index t :=
  ⟨(k.regs .rbx (by decide)).trans h.current,
    (k.regs .r12 (by decide)).trans h.laneLength,
    (k.regs .r13 (by decide)).trans h.segmentLength,
    (k.regs .r14 (by decide)).trans h.slice,
    (k.regs .r15 (by decide)).trans h.index⟩

structure Ready (p : Spec.Argon2.Params) (pass lane slice index : Nat) (s : State) : Prop where
  bounds : Bounds p pass lane slice index
  position : Position p lane slice index s
  lanes : s.gpr .rsi = BitVec.ofNat 64 p.lanes
  passRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp) 8
  passWord : s.mem.readW (s.gpr .rbp) 64 = BitVec.ofNat 64 pass

theorem Ready.lanes_nat {p : Spec.Argon2.Params} {pass lane slice index : Nat} {s : State}
    (h : Ready p pass lane slice index s) : (s.gpr .rsi).toNat = p.lanes := by
  rw [h.lanes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.bounds.lanesBound (by decide))]

theorem Ready.of_keeps {p : Spec.Argon2.Params} {pass lane slice index : Nat} {s t : State}
    (h : Ready p pass lane slice index s) (k : Divide.Keeps changed s t)
    (lanes : t.gpr .rsi = s.gpr .rsi) : Ready p pass lane slice index t := by
  refine ⟨h.bounds, h.position.of_keeps k, lanes.trans h.lanes, ?_, ?_⟩
  · rw [k.rd, k.wr, k.regs .rbp (by decide)]
    exact h.passRead
  · rw [k.mem, k.regs .rbp (by decide)]
    exact h.passWord

def chosenLane (p : Spec.Argon2.Params) (pass lane slice : Nat) (random : Addr) : Nat :=
  if pass = 0 ∧ slice = 0 then lane else (random >>> 32).toNat % p.lanes

theorem chosenLane_bound (p : Spec.Argon2.Params) (pass lane slice : Nat) (random : Addr)
    (positive : 0 < p.lanes) (bound : lane < p.lanes) :
    chosenLane p pass lane slice random < p.lanes := by
  unfold chosenLane
  split
  · exact bound
  · exact Nat.mod_lt _ positive

theorem word_nat (n : Nat) (bound : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

theorem word_zero (n : Nat) (bound : n < 2 ^ 64) : BitVec.ofNat 64 n = (0 : Addr) ↔ n = 0 := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [word_nat n bound] at hn
    exact hn
  · intro h; rw [h]; rfl

theorem word_eq (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x = BitVec.ofNat 64 y ↔ x = y := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [word_nat x hx, word_nat y hy] at hn
    exact hn
  · intro h; rw [h]

theorem Bounds.laneLength_bound {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) : p.laneLen < 2 ^ 32 := by
  have hb : p.laneLen ≤ p.blocks := by
    rw [Proof.Argon2.blocks_lanes p h.lanesPositive]
    exact Nat.le_mul_of_pos_left _ h.lanesPositive
  exact Nat.lt_of_le_of_lt (Nat.le_trans hb (Proof.Argon2.blocks_le_memory p)) h.memoryBound

theorem Bounds.window_positive {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) :
    0 < ReferenceCount.windowBase p pass slice + index ∧
      (index = 0 → 0 < ReferenceCount.windowBase p pass slice) := by
  have hp := Proof.Argon2.reference_count_positive p h.lanesPositive h.memoryMinimum
    pass slice index true h.active (by intro _ _; rfl)
  rw [ReferenceCount.spec_count] at hp
  change 0 < ReferenceCount.windowBase p pass slice + index - 1 at hp
  constructor
  · omega
  · intro zero; rw [zero, Nat.add_zero] at hp; omega

def windowSize (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) : Nat :=
  Spec.Argon2.referenceCount p pass slice index (chosenLane p pass lane slice random == lane)

def windowStart (p : Spec.Argon2.Params) (pass slice : Nat) : Nat :=
  if pass = 0 then 0 else (slice + 1) * p.segmentLen % p.laneLen

def relativeValue (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) : Nat :=
  let count := windowSize p pass lane slice index random
  let j := (random &&& 0xffffffff).toNat
  count - 1 - count * (j * j / 2 ^ 32) / 2 ^ 32

theorem Bounds.segment_le_lane {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) : p.segmentLen ≤ p.laneLen := by
  have segments := Proof.Argon2.laneLen_segments p h.lanesPositive
  omega

theorem Bounds.index_bound64 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) : index < 2 ^ 64 :=
  Nat.lt_trans (Nat.lt_of_lt_of_le h.indexBound h.segment_le_lane)
    (Nat.lt_trans h.laneLength_bound (by decide))

theorem Bounds.chosenLane_bound64 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) (random : Addr) :
    chosenLane p pass lane slice random < 2 ^ 64 :=
  Nat.lt_trans (chosenLane_bound p pass lane slice random h.lanesPositive h.laneBound)
    (Nat.lt_trans h.lanesBound (by decide))

theorem Bounds.lane_bound64 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) : lane < 2 ^ 64 :=
  Nat.lt_trans h.laneBound (Nat.lt_trans h.lanesBound (by decide))

theorem Bounds.windowSize_positive {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) (random : Addr) :
    0 < windowSize p pass lane slice index random := by
  apply Proof.Argon2.reference_count_positive p h.lanesPositive h.memoryMinimum
    pass slice index _ h.active
  intro firstPass firstSlice
  simp only [chosenLane, firstPass, firstSlice, and_self, ite_true]
  exact beq_iff_eq.mpr rfl

theorem Bounds.windowSize_bound32 {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) (random : Addr) :
    windowSize p pass lane slice index random < 2 ^ 32 :=
  Proof.Argon2.reference_count_32 p h.lanesPositive h.memoryMinimum h.memoryBound
    pass slice index _ h.sliceBound h.indexBound

theorem Bounds.windowSize_lt_lane {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) (random : Addr) :
    windowSize p pass lane slice index random < p.laneLen :=
  Proof.Argon2.reference_count_lt_lane p h.lanesPositive h.memoryMinimum
    pass slice index _ h.sliceBound h.indexBound

theorem Bounds.laneLength_positive {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) : 0 < p.laneLen := by
  have seg := Proof.Argon2.segmentLen_ge_two p h.lanesPositive h.memoryMinimum
  have len := Proof.Argon2.laneLen_segments p h.lanesPositive
  omega

theorem Bounds.windowStart_lt_lane {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) : windowStart p pass slice < p.laneLen := by
  unfold windowStart
  split
  · exact h.laneLength_positive
  · exact Nat.mod_lt _ h.laneLength_positive

theorem Bounds.sum_bound {p : Spec.Argon2.Params} {pass lane slice index : Nat}
    (h : Bounds p pass lane slice index) (random : Addr) :
    windowStart p pass slice + relativeValue p pass lane slice index random < 2 * p.laneLen := by
  have start := h.windowStart_lt_lane
  have relative := Proof.Argon2.reference_relative_bound _ (random &&& 0xffffffff).toNat
    (h.windowSize_positive random)
  have count := h.windowSize_lt_lane random
  change relativeValue p pass lane slice index random < windowSize p pass lane slice index random at relative
  omega

end VG.Proof.Argon2.X86_64.ReferenceMap
