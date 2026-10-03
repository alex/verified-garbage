import VerifiedGarbage.Impl.Argon2.AArch64.ReductionInit
import VerifiedGarbage.Proof.Argon2.AArch64.ReductionClear
import VerifiedGarbage.Proof.Argon2.AArch64.ReduceLanes

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
