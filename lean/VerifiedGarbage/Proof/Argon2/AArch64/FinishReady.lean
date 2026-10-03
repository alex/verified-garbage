import VerifiedGarbage.Proof.Argon2.AArch64.FinalOutputReady
import VerifiedGarbage.Impl.Argon2.AArch64.FinalReduction
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
import VerifiedGarbage.Proof.Argon2.AArch64.ClearBlockLit
import VerifiedGarbage.Proof.Argon2.AArch64.ReduceLane
import VerifiedGarbage.Proof.Argon2.AArch64.ReduceBlockLit
import VerifiedGarbage.Proof.Argon2.AArch64.ReducePointers
import VerifiedGarbage.Impl.Argon2.AArch64.ReductionInit
import VerifiedGarbage.Proof.Argon2.AArch64.ReductionLoopState
import VerifiedGarbage.Proof.Argon2.AArch64.ClearBlock
import VerifiedGarbage.Impl.Argon2.AArch64.ReduceLanes
import VerifiedGarbage.Proof.Argon2.AArch64.FillLaneAdvance

/-! Merged from `Proof.Argon2.AArch64.ReduceLanesBody`. -/
section
/-! One reduction iteration advances a public lane and preserves the accumulator invariant. -/

namespace VG.Proof.Argon2.AArch64.ReduceLanes

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (lane : Nat) (s : State) : Prop where
  allocation : ReductionState.Ready p s
  active : lane < p.lanes
  lanesBound : p.lanes < 2 ^ 32
  laneWord : s.gpr .x24 = BitVec.ofNat 64 lane
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

structure Done (s t : State) (p : Params) (lane : Nat) (memory : Array Block) (acc : Block) : Prop where
  represented : ReductionState.Represents p memory acc t
  base : matrix t = matrix s
  laneWord : t.gpr .x24 = BitVec.ofNat 64 (lane + 1)
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp
  cf : eval (.nonzero .x .x14) t = some (decide (lane + 1 < p.lanes))
  next : lane + 1 < p.lanes → Ready p (lane + 1) t

theorem body_ok (s : State) (p : Params) (lane : Nat) (h : Ready p lane s)
    (memory : Array Block) (acc : Block) (represented : ReductionState.Represents p memory acc s) :
    WP isa Impl.Argon2.AArch64.ReduceLanes.body s
      (Done s · p lane memory (xorBlock acc (memory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))) := by
  unfold Impl.Argon2.AArch64.ReduceLanes.body Impl.Argon2.AArch64.ReduceLanes.advance
  refine WP.seq ((ReduceLane.code_ok s p lane h.allocation h.active h.laneWord memory acc represented).mono ?_)
  intro a reduced
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .x19) 184) 8 := by
    rw [reduced.rd, reduced.wr, reduced.regs .x19 (by simp [FillCompress.loopRegs])]; exact h.lanesRead
  have word := (ReductionState.frame_word h.allocation reduced 184 (by decide)).trans h.lanesWord
  have added : a.gpr .x24 + 1 = BitVec.ofNat 64 (lane + 1) := by
    rw [reduced.regs .x24 (by simp [FillCompress.loopRegs]), h.laneWord, BitVec.ofNat_add]; rfl
  have laneBound := h.active
  have lanesBound := h.lanesBound
  have left : (a.gpr .x24 + 1).toNat < 2 ^ 63 := by
    rw [added, ReferenceMap.word_nat (lane + 1) (by omega)]; omega
  have right : (a.mem.readW (off (a.gpr .x19) 184) 64).toNat < 2 ^ 63 := by
    rw [word, ReferenceMap.word_nat p.lanes (by omega)]; omega
  refine (FillLanes.advance_ok a read left right).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have base : matrix t = matrix a := by unfold matrix; rw [keeps.mem, bp]
  have nextWord := value.trans added
  refine ⟨reduced.represented.of_state bp keeps.mem, base.trans reduced.base, nextWord,
    ?_, keeps.rd.trans reduced.rd, keeps.wr.trans reduced.wr, ?_, keeps.sp.trans reduced.sp, ?_, ?_⟩
  · intro r hr bx
    have outside : r ∉ [Reg.x24, .x12, .x13, .x14, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    exact (keeps.regs r outside).trans (reduced.regs r hr)
  · rw [keeps.mem]; exact reduced.frame
  · rw [flag, added, word, ReferenceMap.word_nat (lane + 1) (by have bound := h.lanesBound; have active := h.active; omega),
      ReferenceMap.word_nat p.lanes (Nat.lt_trans h.lanesBound (by decide))]
  · intro active
    refine ⟨reduced.ready.of_state bp (keeps.regs .x20 (by decide)) keeps.mem keeps.rd keeps.wr,
      active, h.lanesBound, nextWord, ?_, ?_⟩
    · rw [keeps.rd, keeps.wr, bp]; exact read
    · rw [keeps.mem, bp]; exact word

end VG.Proof.Argon2.AArch64.ReduceLanes
end

/-! Merged from `Proof.Argon2.AArch64.ReductionInit`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReductionClear`. -/
section
/-! Clear only block zero, preserving the original last blocks in the matrix. -/

namespace VG.Proof.Argon2.AArch64.ReductionState

open VG VG.AArch64 VG.Spec.Argon2

structure Cleared (s t : State) (p : Params) (memory : Array Block) : Prop where
  ready : Ready p t
  represented : Represents p memory zeroBlock t
  base : matrix t = matrix s
  keeps : CopyKeeps s t
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem clear_ok (s : State) (p : Params) (h : Ready p s)
    (dest : s.gpr .x0 = matrix s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.AArch64.ClearBlock.code s (Cleared s · p memory) := by
  have write : Covers [⟨s.gpr .x0, 1024⟩] s.wr := by rw [dest]; exact h.accumulator_cover
  refine (ClearBlock.code_ok s write).mono ?_
  rintro t ⟨zero, frame, keeps, mx⟩
  rw [dest] at frame zero
  have bp := keeps.1 .x19 (by decide) (by decide)
  have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
  have metadata (d : Nat) (bound : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
    rw [bp]
    exact frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact h.frame.symm.sub_right (Region.sub_prefix (by omega))) (by decide)
  have base : matrix t = matrix s := metadata 232 (by decide)
  refine ⟨?_, ?_, base, keeps, frame, mx⟩
  · refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, (keeps.1 .x20 (by decide) (by decide)).trans h.length⟩
    · rw [keeps.2.1, keeps.2.2, bp]; exact h.read
    · rw [base, keeps.2.2]; exact h.write
    · rw [base, bp]; exact h.frame
  · constructor
    · rw [base]; exact zero
    · intro lane active
      rw [base]
      apply Eq.trans _ (represented.block _ (Proof.Argon2.lastIndex_bounds p h.positive h.minimum lane active).2)
      apply FillCompress.block_frame frame
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      have bounds := Proof.Argon2.lastIndex_bounds p h.positive h.minimum lane active
      simpa only [Proof.Argon2.matrixCell, Nat.zero_mul, BitVec.add_zero] using
        Proof.Argon2.matrixCell_disjoint (matrix s) p.blocks (Proof.Argon2.lastIndex p lane) 0 h.bound
          bounds.2 (by omega) (by omega)

theorem Cleared.frame_word {p : Params} {s t : State} {memory : Array Block}
    (ready : Ready p s) (done : Cleared s t p memory) (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.keeps.1 .x19 (by decide) (by decide)]
  exact done.frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ready.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p ready.positive ready.minimum 0 ready.positive
          omega))) (by decide)

end VG.Proof.Argon2.AArch64.ReductionState
end

/-! Merged from `Proof.Argon2.AArch64.ReduceLanes`. -/
section
/-! Termination and correctness of the final lane reduction. -/

namespace VG.Proof.Argon2.AArch64.ReduceLanes

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Finished (s t : State) (p : Params) (memory : Array Block) (acc : Block) : Prop where
  represented : ReductionState.Represents p memory acc t
  base : matrix t = matrix s
  laneWord : t.gpr .x24 = BitVec.ofNat 64 p.lanes
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {lane : Nat} {memory : Array Block} {acc : Block}
    (h : Done s t p lane memory acc) (last : lane + 1 = p.lanes) : Finished s t p memory acc :=
  ⟨h.represented, h.base, last ▸ h.laneWord, h.rd, h.wr, h.frame, h.sp, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {lane : Nat} {memory : Array Block} {acc result : Block}
    (first : Done s a p lane memory acc) (rest : Finished a t p memory result) : Finished s t p memory result := by
  refine ⟨rest.represented, rest.base.trans first.base, rest.laneWord,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.sp.trans first.sp, ?_⟩
  · have frame := rest.frame
    rw [first.base] at frame
    exact first.frame.trans frame
  · intro r hr bx; exact (rest.regs r hr bx).trans (first.regs r hr bx)

theorem loop_ok (count : Nat) (s : State) (p : Params) (lane : Nat) (h : Ready p lane s)
    (memory : Array Block) (acc : Block) (represented : ReductionState.Represents p memory acc s)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    WP isa Impl.Argon2.AArch64.ReduceLanes.loop s
      (Finished s · p memory (Proof.Argon2.reduction p memory lane count acc)) := by
  induction count generalizing s lane acc with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, a, run, done⟩ := body_ok s p lane h memory acc represented
    rw [Proof.Argon2.reduction_succ]
    cases n with
    | zero =>
      have last : lane + 1 = p.lanes := endLane
      refine ⟨_, a, .loopExit run ?_, done.finished last⟩
      simp only [done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : lane + 1 < p.lanes := by omega
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (lane + 1) (done.next active) _
        done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [done.cf, active, decide_true]

end VG.Proof.Argon2.AArch64.ReduceLanes
end

/-! Establish the invariant for reducing all lanes, retaining the input matrix's last blocks. -/

namespace VG.Proof.Argon2.AArch64.ReductionInit

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (s : State) : Prop where
  allocation : ReductionState.Ready p s
  lanesBound : p.lanes < 2 ^ 32
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 184) 8
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

theorem setup_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 232) 8) :
    WP isa (.block Impl.Argon2.AArch64.ReductionInit.setup) s fun t =>
      t.gpr .x0 = matrix s ∧ t.gpr .x24 = 0 ∧ Divide.Keeps [.x0, .x24] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.ReductionInit.setup,
    Impl.Argon2.AArch64.Instructions.load, Impl.Argon2.AArch64.Instructions.imm,
    show 0 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.load, addr, Size.bytes, Size.bits,
    show 232 % 8 = 0 ∧ 232 < 4096 * 8 from by decide, and_self,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (0#16).setWidth 64 = 0#64 from rfl, read, RegUpd.gpr_write,
    reduceCtorEq, ite_false, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

structure Prepared (s t : State) (p : Params) (memory : Array Block) : Prop where
  ready : ReduceLanes.Ready p 0 t
  represented : ReductionState.Represents p memory zeroBlock t
  base : matrix t = matrix s
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  sp : t.sp = s.sp

theorem code_ok (s : State) (p : Params) (h : Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.AArch64.ReductionInit.code s (Prepared s · p memory) := by
  unfold Impl.Argon2.AArch64.ReductionInit.code
  refine WP.seq ((setup_ok s h.allocation.read).mono ?_)
  rintro a ⟨dest, lane, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have base : matrix a = matrix s := by unfold matrix; rw [keeps.mem, bp]
  have ha := h.allocation.of_state bp (keeps.regs .x20 (by decide)) keeps.mem keeps.rd keeps.wr
  have rep : Proof.Argon2.Represents a.mem (matrix a) p.blocks memory := by rw [keeps.mem, base]; exact represented
  refine (ReductionState.clear_ok a p ha (dest.trans base.symm) memory rep).mono ?_
  intro t cleared
  refine ⟨⟨cleared.ready, ha.positive, h.lanesBound,
    (cleared.keeps.1 .x24 (by decide) (by decide)).trans lane, ?_, ?_⟩,
    cleared.represented, cleared.base.trans base, ?_, cleared.keeps.2.1.trans keeps.rd,
    cleared.keeps.2.2.trans keeps.wr, ?_, cleared.sp.trans keeps.sp⟩
  · rw [cleared.keeps.2.1, cleared.keeps.2.2, cleared.keeps.1 .x19 (by decide) (by decide), keeps.rd, keeps.wr, bp]
    exact h.lanesRead
  · rw [cleared.frame_word ha 184 (by decide), keeps.mem, bp]; exact h.lanesWord
  · intro r hr bx
    have ne : r ≠ .x8 ∧ r ≠ .x9 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have notDest : r ≠ .x0 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (cleared.keeps.1 r ne.1 ne.2).trans (keeps.regs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨notDest, bx⟩))
  · have frame := cleared.frame
    rw [base, keeps.mem] at frame; exact frame

end VG.Proof.Argon2.AArch64.ReductionInit
end

/-! Merged from `Proof.Argon2.AArch64.ReductionInitCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReducePointersCT`. -/
section
/-! Pointer preparation reads one public frame location and performs fixed arithmetic. -/

namespace VG.Proof.Argon2.AArch64.ReducePointers

open VG VG.AArch64

theorem code_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    Impl.Argon2.AArch64.ReducePointers.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

end VG.Proof.Argon2.AArch64.ReducePointers
end

/-! Merged from `Proof.Argon2.AArch64.ReduceLanesCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReduceLanesBodyCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReduceLaneCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.ReduceBlockCT`. -/
section
/-! Final block XOR has fixed accesses determined only by its public pointers. -/

namespace VG.Proof.Argon2.AArch64.ReduceBlock

open VG VG.AArch64 VG.Impl.Argon2.AArch64.ReduceBlock

theorem code_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x0, .x1], s.gpr r = t.gpr r)
    code (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x0, .x1])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Argon2.AArch64.ReduceBlock
end

/-! Final lane reduction depends only on public lane coordinates and matrix pointers. -/

namespace VG.Proof.Argon2.AArch64.ReduceLane

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (lane : Nat) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  active : lane < p.lanes
  leftLane : s.gpr .x24 = BitVec.ofNat 64 lane
  rightLane : t.gpr .x24 = BitVec.ofNat 64 lane
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t

theorem pointers_rel (p : Params) (lane : Nat) :
    RelCT isa (Related p lane) Impl.Argon2.AArch64.ReducePointers.code
      (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x0, .x1], s.gpr r = t.gpr r) := by
  have trace := ReducePointers.code_rel.mono (P' := Related p lane) (fun _ _ h => ⟨h.bases, h.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => by
    have q : 0 < p.laneLen := by
      have eq := Proof.Argon2.laneLen_segments p h.left.positive
      have minimum := h.left.minimum
      omega
    exact ⟨ReducePointers.code_ok s lane p.laneLen q h.left.read h.leftLane h.left.length,
      ReducePointers.code_ok t lane p.laneLen q h.right.read h.rightLane h.right.length⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨sp, s, t, hp, ⟨destA, srcA, _⟩, ⟨destB, srcB, _⟩⟩ := h
  refine ⟨sp, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact destA.trans (hp.matrices.trans destB.symm)
  · have bases : s.mem.readW (off (s.gpr .x19) 232) 64 = t.mem.readW (off (t.gpr .x19) 232) 64 := hp.matrices
    rw [srcA, srcB, bases]

theorem code_rel (p : Params) (lane : Nat) :
    RelCT isa (Related p lane) Impl.Argon2.AArch64.ReduceLane.code (fun _ _ => True) :=
  (pointers_rel p lane).seq ReduceBlock.code_rel

end VG.Proof.Argon2.AArch64.ReduceLane
end

/-! Reduction visits the same last blocks even when their contents differ. -/

namespace VG.Proof.Argon2.AArch64.ReduceLanes

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (lane : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block)
    (s t : State) : Prop where
  left : Ready p lane s
  right : Ready p lane t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t
  leftRep : ReductionState.Represents p leftMemory leftAcc s
  rightRep : ReductionState.Represents p rightMemory rightAcc t

theorem advance_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.ReduceLanes.advance) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem body_rel (p : Params) (lane : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block) :
    RelCT isa (Related p lane leftMemory rightMemory leftAcc rightAcc) Impl.Argon2.AArch64.ReduceLanes.body
      (fun s t => eval (.nonzero .x .x14) s = eval (.nonzero .x .x14) t ∧ (lane + 1 < p.lanes → Related p (lane + 1) leftMemory rightMemory
        (xorBlock leftAcc (leftMemory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))
        (xorBlock rightAcc (rightMemory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock)) s t)) := by
  intro s t ts tt a b hp ea eb
  have related : ReduceLane.Related p lane s t :=
    ⟨hp.left.allocation, hp.right.allocation, hp.left.active, hp.left.laneWord, hp.right.laneWord, hp.bases, hp.stacks, hp.matrices⟩
  cases ea with
  | seq reduceA advanceA =>
    cases eb with
    | seq reduceB advanceB =>
      obtain ⟨reduceTrace, _⟩ := ReduceLane.code_rel p lane _ _ _ _ _ _ related reduceA reduceB
      obtain ⟨_, sa, runA, reducedA⟩ := ReduceLane.code_ok s p lane hp.left.allocation hp.left.active
        hp.left.laneWord leftMemory leftAcc hp.leftRep
      obtain ⟨_, sb, runB, reducedB⟩ := ReduceLane.code_ok t p lane hp.right.allocation hp.right.active
        hp.right.laneWord rightMemory rightAcc hp.rightRep
      obtain ⟨_, rfl⟩ := Exec.det reduceA runA
      obtain ⟨_, rfl⟩ := Exec.det reduceB runB
      have bases := (reducedA.regs .x19 (by simp [FillCompress.loopRegs])).trans
        (hp.bases.trans (reducedB.regs .x19 (by simp [FillCompress.loopRegs])).symm)
      have stacks := reducedA.sp.trans (hp.stacks.trans reducedB.sp.symm)
      obtain ⟨advanceTrace, _⟩ := advance_rel _ _ _ _ _ _ ⟨bases, stacks⟩ advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p lane hp.left leftMemory leftAcc hp.leftRep
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p lane hp.right rightMemory rightAcc hp.rightRep
      obtain ⟨_, rfl⟩ := Exec.det (.seq reduceA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq reduceB advanceB) runB
      refine ⟨by rw [reduceTrace, advanceTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_, doneA.sp.trans (hp.stacks.trans doneB.sp.symm),
        doneA.base.trans (hp.matrices.trans doneB.base.symm), doneA.represented, doneB.represented⟩
      exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).trans
        (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).symm)

end VG.Proof.Argon2.AArch64.ReduceLanes
end

/-! The final reduction leaks only public matrix addresses and the public lane count. -/

namespace VG.Proof.Argon2.AArch64.ReduceLanes

open VG VG.AArch64 VG.Spec.Argon2

theorem loop_rel (p : Params) (lane count : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    RelCT isa (Related p lane leftMemory rightMemory leftAcc rightAcc) Impl.Argon2.AArch64.ReduceLanes.loop
      (fun _ _ => True) := by
  let I := fun n s t => ∃ (lane : Nat) (leftAcc rightAcc : Block), lane + n = p.lanes ∧ 0 < n ∧
    Related p lane leftMemory rightMemory leftAcc rightAcc s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.AArch64.ReduceLanes.body fun s t =>
      isa.eval (.nonzero .x .x14) s = isa.eval (.nonzero .x .x14) t ∧ (isa.eval (.nonzero .x .x14) s = some false → True) ∧
        (isa.eval (.nonzero .x .x14) s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, la, ra, endLane, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨trace, flags, next⟩ := body_rel p j leftMemory rightMemory la ra _ _ _ _ _ _ hp ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p j hp.left leftMemory la hp.leftRep
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · exact flags
      · intro taken
        have active : j + 1 < p.lanes := by
          simp only [done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        exact ⟨n, by omega, j + 1, _, _, by omega, by omega, next active⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨lane, leftAcc, rightAcc, endLane, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.ReduceLanes
end

/-! Clearing the accumulator follows public pointers and visits a fixed block. -/

namespace VG.Proof.Argon2.AArch64.ReductionInit

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftMemory rightMemory : Array Block) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .x19 = t.gpr .x19
  stacks : s.sp = t.sp
  matrices : matrix s = matrix t
  leftMatrix : Proof.Argon2.Represents s.mem (matrix s) p.blocks leftMemory
  rightMatrix : Proof.Argon2.Represents t.mem (matrix t) p.blocks rightMemory

theorem setup_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block Impl.Argon2.AArch64.ReductionInit.setup) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem clear_rel : RelCT isa (fun s t => s.gpr .x0 = t.gpr .x0 ∧ s.sp = t.sp)
    Impl.Argon2.AArch64.ClearBlock.code (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x0])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem code_rel (p : Params) (leftMemory rightMemory : Array Block) :
    RelCT isa (Related p leftMemory rightMemory) Impl.Argon2.AArch64.ReductionInit.code
      (ReduceLanes.Related p 0 leftMemory rightMemory zeroBlock zeroBlock) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq setupA clearA =>
    cases eb with
    | seq setupB clearB =>
      obtain ⟨setupTrace, setupSp⟩ := setup_rel _ _ _ _ _ _ ⟨hp.bases, hp.stacks⟩ setupA setupB
      obtain ⟨_, sa, runA, destA, _, _⟩ := setup_ok s hp.left.allocation.read
      obtain ⟨_, sb, runB, destB, _, _⟩ := setup_ok t hp.right.allocation.read
      obtain ⟨_, rfl⟩ := Exec.det setupA runA
      obtain ⟨_, rfl⟩ := Exec.det setupB runB
      obtain ⟨clearTrace, _⟩ := clear_rel _ _ _ _ _ _ ⟨destA.trans (hp.matrices.trans destB.symm), setupSp⟩ clearA clearB
      obtain ⟨_, a', runA, doneA⟩ := code_ok s p hp.left leftMemory hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := code_ok t p hp.right rightMemory hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq setupA clearA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq setupB clearB) runB
      refine ⟨by rw [setupTrace, clearTrace], doneA.ready, doneB.ready, ?_, doneA.sp.trans (hp.stacks.trans doneB.sp.symm),
        doneA.base.trans (hp.matrices.trans doneB.base.symm), doneA.represented, doneB.represented⟩
      exact (doneA.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).trans
        (hp.bases.trans (doneB.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)).symm)

end VG.Proof.Argon2.AArch64.ReductionInit
end

/-! Merged from `Proof.Argon2.AArch64.FinalReduction`. -/
section
/-! Complete final block reduction, including setup, termination and a public trace. -/

namespace VG.Proof.Argon2.AArch64.FinalReduction

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

theorem code_ok (s : State) (p : Params) (h : ReductionInit.Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.AArch64.FinalReduction.code s
      (ReduceLanes.Finished s · p memory (Proof.Argon2.reduction p memory 0 p.lanes zeroBlock)) := by
  unfold Impl.Argon2.AArch64.FinalReduction.code
  refine WP.seq ((ReductionInit.code_ok s p h memory represented).mono ?_)
  intro a prepared
  refine (ReduceLanes.loop_ok p.lanes a p 0 prepared.ready memory zeroBlock prepared.represented
    h.allocation.positive (Nat.zero_add _)).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.base.trans prepared.base, finished.laneWord,
    finished.rd.trans prepared.rd, finished.wr.trans prepared.wr, ?_, finished.sp.trans prepared.sp, ?_⟩
  · have frame := finished.frame
    rw [prepared.base] at frame
    exact prepared.frame.trans frame
  · intro r hr bx; exact (finished.regs r hr bx).trans (prepared.regs r hr bx)

theorem code_rel (p : Params) (positive : 0 < p.lanes) (leftMemory rightMemory : Array Block) :
    RelCT isa (ReductionInit.Related p leftMemory rightMemory) Impl.Argon2.AArch64.FinalReduction.code
      (fun _ _ => True) :=
  (ReductionInit.code_rel p leftMemory rightMemory).seq
    (ReduceLanes.loop_rel p 0 p.lanes leftMemory rightMemory zeroBlock zeroBlock positive (Nat.zero_add _))

end VG.Proof.Argon2.AArch64.FinalReduction
end

/-! Preserve the final-call allocations and metadata through the matrix reduction. -/

namespace VG.Proof.Argon2.AArch64.Finish

open VG VG.AArch64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (s : State) : Prop where
  reduction : ReductionInit.Ready p s
  output : FinalOutput.Ready p s

theorem frame_word {s t : State} {p : Params} {memory : Array Block} {acc : Block}
    (ready : ReductionInit.Ready p s) (done : ReduceLanes.Finished s t p memory acc)
    (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)]
  exact done.frame.readW (r := ⟨s.gpr .x19, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ready.allocation.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p ready.allocation.positive ready.allocation.minimum 0 ready.allocation.positive
          omega))) (by decide)

theorem output_ready {s t : State} {p : Params} {memory : Array Block} {acc : Block}
    (ready : Ready p s) (done : ReduceLanes.Finished s t p memory acc) : FinalOutput.Ready p t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide)
  have sp := done.sp
  have output : FinalOutput.output t = FinalOutput.output s := frame_word ready.reduction done 256 (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := frame_word ready.reduction done 248 (by decide)
  refine ⟨?_, ready.output.positive, ready.output.bound, ?_,
    (frame_word ready.reduction done 264 (by decide)).trans ready.output.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sp]; exact ready.output.stackMinimum
  · rw [done.rd, done.wr, bp]; exact ready.output.reads
  · rw [done.base, done.rd, done.wr]; exact ready.output.input
  · rw [output, done.wr]; exact ready.output.outputWrite
  · rw [work, done.wr]; exact ready.output.workWrite
  · rw [done.base, work]; exact ready.output.inputWork
  · rw [output, work]; exact ready.output.outputWork
  · rw [sp, done.base]; exact ready.output.stackInput
  · rw [sp, output]; exact ready.output.stackOutput
  · rw [sp, work]; exact ready.output.stackWork

end VG.Proof.Argon2.AArch64.Finish
