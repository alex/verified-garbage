import VerifiedGarbage.Impl.Argon2.X86_64.ReduceLanes
import VerifiedGarbage.Proof.Argon2.X86_64.ReductionLoopState
import VerifiedGarbage.Proof.Argon2.X86_64.FillLaneAdvance

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
