import VerifiedGarbage.Proof.Argon2.X86_64.FinalOutputReady
import VerifiedGarbage.Impl.Argon2.X86_64.FinalReduction
import VerifiedGarbage.Proof.Argon2.X86_64.ClearBlockLit
import VerifiedGarbage.Proof.Argon2.X86_64.ReduceLane
import VerifiedGarbage.Proof.Argon2.X86_64.ReduceBlockLit
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Argon2.X86_64.ReducePointers
import VerifiedGarbage.Impl.Argon2.X86_64.ReductionInit
import VerifiedGarbage.Proof.Argon2.X86_64.ReductionLoopState
import VerifiedGarbage.Proof.Argon2.X86_64.ClearBlock
import VerifiedGarbage.Impl.Argon2.X86_64.ReduceLanes
import VerifiedGarbage.Proof.Argon2.X86_64.FillLaneAdvance

/-! Merged from `Proof.Argon2.X86_64.ReduceLanesBody`. -/
section
/-! One reduction iteration advances a public lane and preserves the accumulator invariant. -/

namespace VG.Proof.Argon2.X86_64.ReduceLanes

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (lane : Nat) (s : State) : Prop where
  allocation : ReductionState.Ready p s
  active : lane < p.lanes
  lanesBound : p.lanes < 2 ^ 32
  laneWord : s.gpr .rbx = BitVec.ofNat 64 lane
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 184) 8
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

structure Done (s t : State) (p : Params) (lane : Nat) (memory : Array Block) (acc : Block) : Prop where
  represented : ReductionState.Represents p memory acc t
  base : matrix t = matrix s
  laneWord : t.gpr .rbx = BitVec.ofNat 64 (lane + 1)
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  cf : t.cf = decide (lane + 1 < p.lanes)
  next : lane + 1 < p.lanes → Ready p (lane + 1) t

theorem body_ok (s : State) (p : Params) (lane : Nat) (h : Ready p lane s)
    (memory : Array Block) (acc : Block) (represented : ReductionState.Represents p memory acc s) :
    WP isa Impl.Argon2.X86_64.ReduceLanes.body s
      (Done s · p lane memory (xorBlock acc (memory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))) := by
  unfold Impl.Argon2.X86_64.ReduceLanes.body Impl.Argon2.X86_64.ReduceLanes.advance
  refine WP.seq ((ReduceLane.code_ok s p lane h.allocation h.active h.laneWord memory acc represented).mono ?_)
  intro a reduced
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) 184) 8 := by
    rw [reduced.rd, reduced.wr, reduced.regs .rbp (by simp [calleeSaved])]; exact h.lanesRead
  have word := (ReductionState.frame_word h.allocation reduced 184 (by decide)).trans h.lanesWord
  refine (FillLanes.advance_ok a read).mono ?_
  rintro t ⟨value, flag, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have base : matrix t = matrix a := by unfold matrix; rw [keeps.mem, bp]
  have added : a.gpr .rbx + 1 = BitVec.ofNat 64 (lane + 1) := by
    rw [reduced.regs .rbx (by simp [calleeSaved]), h.laneWord, BitVec.ofNat_add]; rfl
  have nextWord := value.trans added
  refine ⟨reduced.represented.of_state bp keeps.mem, base.trans reduced.base, nextWord,
    ?_, keeps.rd.trans reduced.rd, keeps.wr.trans reduced.wr, ?_, keeps.mxcsr.trans reduced.mxcsr, ?_, ?_⟩
  · intro r hr bx
    exact (keeps.regs r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using bx)).trans (reduced.regs r hr)
  · rw [keeps.mem]; exact reduced.frame
  · rw [flag, added, word, ReferenceMap.word_nat (lane + 1) (by have bound := h.lanesBound; have active := h.active; omega),
      ReferenceMap.word_nat p.lanes (Nat.lt_trans h.lanesBound (by decide))]
  · intro active
    refine ⟨reduced.ready.of_state bp (keeps.regs .r12 (by decide)) keeps.mem keeps.rd keeps.wr,
      active, h.lanesBound, nextWord, ?_, ?_⟩
    · rw [keeps.rd, keeps.wr, bp]; exact read
    · rw [keeps.mem, bp]; exact word

end VG.Proof.Argon2.X86_64.ReduceLanes
end

/-! Merged from `Proof.Argon2.X86_64.ReductionInit`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReductionClear`. -/
section
/-! Clear only block zero, preserving the original last blocks in the matrix. -/

namespace VG.Proof.Argon2.X86_64.ReductionState

open VG VG.X86_64 VG.Spec.Argon2

structure Cleared (s t : State) (p : Params) (memory : Array Block) : Prop where
  ready : Ready p t
  represented : Represents p memory zeroBlock t
  base : matrix t = matrix s
  keeps : CopyKeeps s t
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem clear_ok (s : State) (p : Params) (h : Ready p s)
    (dest : s.gpr .rdi = matrix s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.X86_64.ClearBlock.code s (Cleared s · p memory) := by
  have write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr := by rw [dest]; exact h.accumulator_cover
  refine (ClearBlock.code_ok s write).mono ?_
  rintro t ⟨zero, frame, keeps, mx⟩
  rw [dest] at frame zero
  have bp := keeps.1 .rbp (by decide)
  have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
  have metadata (d : Nat) (bound : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
    rw [bp]
    exact frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact h.frame.symm.sub_right (Region.sub_prefix (by omega))) (by decide)
  have base : matrix t = matrix s := metadata 232 (by decide)
  refine ⟨?_, ?_, base, keeps, frame, mx⟩
  · refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, (keeps.1 .r12 (by decide)).trans h.length⟩
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
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [done.keeps.1 .rbp (by decide)]
  exact done.frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ready.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p ready.positive ready.minimum 0 ready.positive
          omega))) (by decide)

end VG.Proof.Argon2.X86_64.ReductionState
end

/-! Merged from `Proof.Argon2.X86_64.ReduceLanes`. -/
section
/-! Termination and correctness of the final lane reduction. -/

namespace VG.Proof.Argon2.X86_64.ReduceLanes

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Finished (s t : State) (p : Params) (memory : Array Block) (acc : Block) : Prop where
  represented : ReductionState.Represents p memory acc t
  base : matrix t = matrix s
  laneWord : t.gpr .rbx = BitVec.ofNat 64 p.lanes
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → t.gpr r = s.gpr r

theorem Done.finished {s t : State} {p : Params} {lane : Nat} {memory : Array Block} {acc : Block}
    (h : Done s t p lane memory acc) (last : lane + 1 = p.lanes) : Finished s t p memory acc :=
  ⟨h.represented, h.base, last ▸ h.laneWord, h.rd, h.wr, h.frame, h.mxcsr, h.regs⟩

theorem Finished.prepend {s a t : State} {p : Params} {lane : Nat} {memory : Array Block} {acc result : Block}
    (first : Done s a p lane memory acc) (rest : Finished a t p memory result) : Finished s t p memory result := by
  refine ⟨rest.represented, rest.base.trans first.base, rest.laneWord,
    rest.rd.trans first.rd, rest.wr.trans first.wr, ?_, rest.mxcsr.trans first.mxcsr, ?_⟩
  · have frame := rest.frame
    rw [first.base] at frame
    exact first.frame.trans frame
  · intro r hr bx; exact (rest.regs r hr bx).trans (first.regs r hr bx)

theorem loop_ok (count : Nat) (s : State) (p : Params) (lane : Nat) (h : Ready p lane s)
    (memory : Array Block) (acc : Block) (represented : ReductionState.Represents p memory acc s)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    WP isa Impl.Argon2.X86_64.ReduceLanes.loop s
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
      simp only [eval, done.cf, last, Nat.lt_irrefl, decide_false]
    | succ n =>
      have active : lane + 1 < p.lanes := by omega
      obtain ⟨restTrace, t, restRun, finished⟩ := ih a (lane + 1) (done.next active) _
        done.represented (by omega) (by omega)
      refine ⟨_, t, .loopNext run ?_ restRun, finished.prepend done⟩
      simp only [eval, done.cf, active, decide_true]

end VG.Proof.Argon2.X86_64.ReduceLanes
end

/-! Establish the invariant for reducing all lanes, retaining the input matrix's last blocks. -/

namespace VG.Proof.Argon2.X86_64.ReductionInit

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (s : State) : Prop where
  allocation : ReductionState.Ready p s
  lanesBound : p.lanes < 2 ^ 32
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 184) 8
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes

theorem setup_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 232) 8) :
    WP isa (.block Impl.Argon2.X86_64.ReductionInit.setup) s fun t =>
      t.gpr .rdi = matrix s ∧ t.gpr .rbx = 0 ∧ Divide.Keeps [.rdi, .rbx] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.ReductionInit.setup, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_at, read, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg, reduceCtorEq, ite_false]
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  all_goals rfl

structure Prepared (s t : State) (p : Params) (memory : Array Block) : Prop where
  ready : ReduceLanes.Ready p 0 t
  represented : ReductionState.Represents p memory zeroBlock t
  base : matrix t = matrix s
  regs : ∀ r ∈ calleeSaved, r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨matrix s, 1024⟩] s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem code_ok (s : State) (p : Params) (h : Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.X86_64.ReductionInit.code s (Prepared s · p memory) := by
  unfold Impl.Argon2.X86_64.ReductionInit.code
  refine WP.seq ((setup_ok s h.allocation.read).mono ?_)
  rintro a ⟨dest, lane, keeps⟩
  have bp := keeps.regs .rbp (by decide)
  have base : matrix a = matrix s := by unfold matrix; rw [keeps.mem, bp]
  have ha := h.allocation.of_state bp (keeps.regs .r12 (by decide)) keeps.mem keeps.rd keeps.wr
  have rep : Proof.Argon2.Represents a.mem (matrix a) p.blocks memory := by rw [keeps.mem, base]; exact represented
  refine (ReductionState.clear_ok a p ha (dest.trans base.symm) memory rep).mono ?_
  intro t cleared
  refine ⟨⟨cleared.ready, ha.positive, h.lanesBound,
    (cleared.keeps.1 .rbx (by decide)).trans lane, ?_, ?_⟩,
    cleared.represented, cleared.base.trans base, ?_, cleared.keeps.2.1.trans keeps.rd,
    cleared.keeps.2.2.trans keeps.wr, ?_, cleared.mxcsr.trans keeps.mxcsr⟩
  · rw [cleared.keeps.2.1, cleared.keeps.2.2, cleared.keeps.1 .rbp (by decide), keeps.rd, keeps.wr, bp]
    exact h.lanesRead
  · rw [cleared.frame_word ha 184 (by decide), keeps.mem, bp]; exact h.lanesWord
  · intro r hr bx
    have ne : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have notDest : r ≠ .rdi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (cleared.keeps.1 r ne).trans (keeps.regs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨notDest, bx⟩))
  · have frame := cleared.frame
    rw [base, keeps.mem] at frame; exact frame

end VG.Proof.Argon2.X86_64.ReductionInit
end

/-! Merged from `Proof.Argon2.X86_64.ReductionInitCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReducePointersCT`. -/
section
/-! Pointer preparation reads one public frame location and performs fixed arithmetic. -/

namespace VG.Proof.Argon2.X86_64.ReducePointers

open VG VG.X86_64

theorem code_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    Impl.Argon2.X86_64.ReducePointers.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

end VG.Proof.Argon2.X86_64.ReducePointers
end

/-! Merged from `Proof.Argon2.X86_64.ReduceLanesCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReduceLanesBodyCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReduceLaneCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.ReduceBlockCT`. -/
section
/-! Final block XOR has fixed accesses determined only by its public pointers. -/

namespace VG.Proof.Argon2.X86_64.ReduceBlock

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReduceBlock

theorem code_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rdi, .rsi], s.gpr r = t.gpr r) code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

end VG.Proof.Argon2.X86_64.ReduceBlock
end

/-! Final lane reduction depends only on public lane coordinates and matrix pointers. -/

namespace VG.Proof.Argon2.X86_64.ReduceLane

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (lane : Nat) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  active : lane < p.lanes
  leftLane : s.gpr .rbx = BitVec.ofNat 64 lane
  rightLane : t.gpr .rbx = BitVec.ofNat 64 lane
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : matrix s = matrix t

theorem pointers_rel (p : Params) (lane : Nat) :
    RelCT isa (Related p lane) Impl.Argon2.X86_64.ReducePointers.code
      (fun s t => ∀ r ∈ [Reg.rdi, .rsi], s.gpr r = t.gpr r) := by
  have trace := ReducePointers.code_rel.mono (P' := Related p lane) (fun _ _ h => h.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h => by
    have q : 0 < p.laneLen := by
      have eq := Proof.Argon2.laneLen_segments p h.left.positive
      have minimum := h.left.minimum
      omega
    exact ⟨ReducePointers.code_ok s lane p.laneLen q h.left.read h.leftLane h.left.length,
      ReducePointers.code_ok t lane p.laneLen q h.right.read h.rightLane h.right.length⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨destA, srcA, _⟩, ⟨destB, srcB, _⟩⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact destA.trans (hp.matrices.trans destB.symm)
  · have bases : s.mem.readW (off (s.gpr .rbp) 232) 64 = t.mem.readW (off (t.gpr .rbp) 232) 64 := hp.matrices
    rw [srcA, srcB, bases]

theorem code_rel (p : Params) (lane : Nat) :
    RelCT isa (Related p lane) Impl.Argon2.X86_64.ReduceLane.code (fun _ _ => True) :=
  (pointers_rel p lane).seq ReduceBlock.code_rel

end VG.Proof.Argon2.X86_64.ReduceLane
end

/-! Reduction visits the same last blocks even when their contents differ. -/

namespace VG.Proof.Argon2.X86_64.ReduceLanes

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (lane : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block)
    (s t : State) : Prop where
  left : Ready p lane s
  right : Ready p lane t
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : matrix s = matrix t
  leftRep : ReductionState.Represents p leftMemory leftAcc s
  rightRep : ReductionState.Represents p rightMemory rightAcc t

theorem advance_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.ReduceLanes.advance) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem body_rel (p : Params) (lane : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block) :
    RelCT isa (Related p lane leftMemory rightMemory leftAcc rightAcc) Impl.Argon2.X86_64.ReduceLanes.body
      (fun s t => s.cf = t.cf ∧ (lane + 1 < p.lanes → Related p (lane + 1) leftMemory rightMemory
        (xorBlock leftAcc (leftMemory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))
        (xorBlock rightAcc (rightMemory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock)) s t)) := by
  intro s t ts tt a b hp ea eb
  have related : ReduceLane.Related p lane s t :=
    ⟨hp.left.allocation, hp.right.allocation, hp.left.active, hp.left.laneWord, hp.right.laneWord, hp.bases, hp.matrices⟩
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
      have bases := (reducedA.regs .rbp (by simp [calleeSaved])).trans
        (hp.bases.trans (reducedB.regs .rbp (by simp [calleeSaved])).symm)
      obtain ⟨advanceTrace, _⟩ := advance_rel _ _ _ _ _ _ bases advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p lane hp.left leftMemory leftAcc hp.leftRep
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p lane hp.right rightMemory rightAcc hp.rightRep
      obtain ⟨_, rfl⟩ := Exec.det (.seq reduceA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq reduceB advanceB) runB
      refine ⟨by rw [reduceTrace, advanceTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_,
        doneA.base.trans (hp.matrices.trans doneB.base.symm), doneA.represented, doneB.represented⟩
      exact (doneA.regs .rbp (by simp [calleeSaved]) (by decide)).trans
        (hp.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide)).symm)

end VG.Proof.Argon2.X86_64.ReduceLanes
end

/-! The final reduction leaks only public matrix addresses and the public lane count. -/

namespace VG.Proof.Argon2.X86_64.ReduceLanes

open VG VG.X86_64 VG.Spec.Argon2

theorem loop_rel (p : Params) (lane count : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block)
    (positive : 0 < count) (endLane : lane + count = p.lanes) :
    RelCT isa (Related p lane leftMemory rightMemory leftAcc rightAcc) Impl.Argon2.X86_64.ReduceLanes.loop
      (fun _ _ => True) := by
  let I := fun n s t => ∃ (lane : Nat) (leftAcc rightAcc : Block), lane + n = p.lanes ∧ 0 < n ∧
    Related p lane leftMemory rightMemory leftAcc rightAcc s t
  have steps : ∀ n, RelCT isa (I n) Impl.Argon2.X86_64.ReduceLanes.body fun s t =>
      isa.eval .b s = isa.eval .b t ∧ (isa.eval .b s = some false → True) ∧
        (isa.eval .b s = some true → ∃ m < n, I m s t) := by
    intro n s t ts tt a b hp ea eb
    obtain ⟨j, la, ra, endLane, positive, hp⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨trace, flags, next⟩ := body_rel p j leftMemory rightMemory la ra _ _ _ _ _ _ hp ea eb
      obtain ⟨_, a', runA, done⟩ := body_ok s p j hp.left leftMemory la hp.leftRep
      obtain ⟨_, rfl⟩ := Exec.det ea runA
      refine ⟨trace, ?_, fun _ => trivial, ?_⟩
      · simp only [eval, flags]
      · intro taken
        have active : j + 1 < p.lanes := by
          simp only [eval, done.cf, Option.some.injEq, decide_eq_true_eq] at taken
          exact taken
        exact ⟨n, by omega, j + 1, _, _, by omega, by omega, next active⟩
  exact (RelCT.loop I steps count).mono
    (fun _ _ h => ⟨lane, leftAcc, rightAcc, endLane, positive, h⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.ReduceLanes
end

/-! Clearing the accumulator follows public pointers and visits a fixed block. -/

namespace VG.Proof.Argon2.X86_64.ReductionInit

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (leftMemory rightMemory : Array Block) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : matrix s = matrix t
  leftMatrix : Proof.Argon2.Represents s.mem (matrix s) p.blocks leftMemory
  rightMatrix : Proof.Argon2.Represents t.mem (matrix t) p.blocks rightMemory

theorem setup_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.ReductionInit.setup) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem clear_rel : RelCT isa (fun s t => s.gpr .rdi = t.gpr .rdi)
    Impl.Argon2.X86_64.ClearBlock.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rdi])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem code_rel (p : Params) (leftMemory rightMemory : Array Block) :
    RelCT isa (Related p leftMemory rightMemory) Impl.Argon2.X86_64.ReductionInit.code
      (ReduceLanes.Related p 0 leftMemory rightMemory zeroBlock zeroBlock) := by
  intro s t ts tt a b hp ea eb
  cases ea with
  | seq setupA clearA =>
    cases eb with
    | seq setupB clearB =>
      obtain ⟨setupTrace, _⟩ := setup_rel _ _ _ _ _ _ hp.bases setupA setupB
      obtain ⟨_, sa, runA, destA, _, _⟩ := setup_ok s hp.left.allocation.read
      obtain ⟨_, sb, runB, destB, _, _⟩ := setup_ok t hp.right.allocation.read
      obtain ⟨_, rfl⟩ := Exec.det setupA runA
      obtain ⟨_, rfl⟩ := Exec.det setupB runB
      obtain ⟨clearTrace, _⟩ := clear_rel _ _ _ _ _ _ (destA.trans (hp.matrices.trans destB.symm)) clearA clearB
      obtain ⟨_, a', runA, doneA⟩ := code_ok s p hp.left leftMemory hp.leftMatrix
      obtain ⟨_, b', runB, doneB⟩ := code_ok t p hp.right rightMemory hp.rightMatrix
      obtain ⟨_, rfl⟩ := Exec.det (.seq setupA clearA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq setupB clearB) runB
      refine ⟨by rw [setupTrace, clearTrace], doneA.ready, doneB.ready, ?_,
        doneA.base.trans (hp.matrices.trans doneB.base.symm), doneA.represented, doneB.represented⟩
      exact (doneA.regs .rbp (by simp [calleeSaved]) (by decide)).trans
        (hp.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide)).symm)

end VG.Proof.Argon2.X86_64.ReductionInit
end

/-! Merged from `Proof.Argon2.X86_64.FinalReduction`. -/
section
/-! Complete final block reduction, including setup, termination and a public trace. -/

namespace VG.Proof.Argon2.X86_64.FinalReduction

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

theorem code_ok (s : State) (p : Params) (h : ReductionInit.Ready p s) (memory : Array Block)
    (represented : Proof.Argon2.Represents s.mem (matrix s) p.blocks memory) :
    WP isa Impl.Argon2.X86_64.FinalReduction.code s
      (ReduceLanes.Finished s · p memory (Proof.Argon2.reduction p memory 0 p.lanes zeroBlock)) := by
  unfold Impl.Argon2.X86_64.FinalReduction.code
  refine WP.seq ((ReductionInit.code_ok s p h memory represented).mono ?_)
  intro a prepared
  refine (ReduceLanes.loop_ok p.lanes a p 0 prepared.ready memory zeroBlock prepared.represented
    h.allocation.positive (Nat.zero_add _)).mono ?_
  intro t finished
  refine ⟨finished.represented, finished.base.trans prepared.base, finished.laneWord,
    finished.rd.trans prepared.rd, finished.wr.trans prepared.wr, ?_, finished.mxcsr.trans prepared.mxcsr, ?_⟩
  · have frame := finished.frame
    rw [prepared.base] at frame
    exact prepared.frame.trans frame
  · intro r hr bx; exact (finished.regs r hr bx).trans (prepared.regs r hr bx)

theorem code_rel (p : Params) (positive : 0 < p.lanes) (leftMemory rightMemory : Array Block) :
    RelCT isa (ReductionInit.Related p leftMemory rightMemory) Impl.Argon2.X86_64.FinalReduction.code
      (fun _ _ => True) :=
  (ReductionInit.code_rel p leftMemory rightMemory).seq
    (ReduceLanes.loop_rel p 0 p.lanes leftMemory rightMemory zeroBlock zeroBlock positive (Nat.zero_add _))

end VG.Proof.Argon2.X86_64.FinalReduction
end

/-! Preserve the final-call allocations and metadata through the matrix reduction. -/

namespace VG.Proof.Argon2.X86_64.Finish

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Ready (p : Params) (s : State) : Prop where
  reduction : ReductionInit.Ready p s
  output : FinalOutput.Ready p s

theorem frame_word {s t : State} {p : Params} {memory : Array Block} {acc : Block}
    (ready : ReductionInit.Ready p s) (done : ReduceLanes.Finished s t p memory acc)
    (d : Nat) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [done.regs .rbp (by simp [calleeSaved]) (by decide)]
  exact done.frame.readW (r := ⟨s.gpr .rbp, 272⟩) (Offset.contains_base _ bound (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ready.allocation.frame.symm.sub_right (Region.sub_prefix (by
          have nonempty := Proof.Argon2.lastIndex_bounds p ready.allocation.positive ready.allocation.minimum 0 ready.allocation.positive
          omega))) (by decide)

theorem output_ready {s t : State} {p : Params} {memory : Array Block} {acc : Block}
    (ready : Ready p s) (done : ReduceLanes.Finished s t p memory acc) : FinalOutput.Ready p t := by
  have bp := done.regs .rbp (by simp [calleeSaved]) (by decide)
  have sp := done.regs .rsp (by simp [calleeSaved]) (by decide)
  have output : FinalOutput.output t = FinalOutput.output s := frame_word ready.reduction done 256 (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := frame_word ready.reduction done 248 (by decide)
  refine ⟨ready.output.positive, ready.output.bound, ?_,
    (frame_word ready.reduction done 264 (by decide)).trans ready.output.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [done.rd, done.wr, bp]; exact ready.output.reads
  · rw [done.base, done.rd, done.wr]; exact ready.output.input
  · rw [output, done.wr]; exact ready.output.outputWrite
  · rw [work, done.wr]; exact ready.output.workWrite
  · rw [done.base, work]; exact ready.output.inputWork
  · rw [output, work]; exact ready.output.outputWork
  · rw [sp, done.base]; exact ready.output.stackInput
  · rw [sp, output]; exact ready.output.stackOutput
  · rw [sp, work]; exact ready.output.stackWork

end VG.Proof.Argon2.X86_64.Finish
