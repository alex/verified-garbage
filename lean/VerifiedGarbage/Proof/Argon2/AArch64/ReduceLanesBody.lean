import VerifiedGarbage.Impl.Argon2.AArch64.ReduceLanes
import VerifiedGarbage.Proof.Argon2.AArch64.ReductionLoopState
import VerifiedGarbage.Proof.Argon2.AArch64.FillLaneAdvance

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
