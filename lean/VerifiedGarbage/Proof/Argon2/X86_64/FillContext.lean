import VerifiedGarbage.Proof.Argon2.X86_64.FillSegment

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
