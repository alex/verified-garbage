import VerifiedGarbage.Proof.Argon2.AArch64.ReduceBlock
import VerifiedGarbage.Proof.Argon2.AArch64.ReducePointers

/-! Block zero is the accumulator; every lane's last block remains unchanged. -/

namespace VG.Proof.Argon2.AArch64.ReductionState

open VG VG.AArch64 VG.Spec.Argon2

def matrix (s : State) : Addr := s.mem.readW (off (s.gpr .x19) 232) 64

structure Ready (p : Params) (s : State) : Prop where
  positive : 0 < p.lanes
  minimum : 2 ≤ p.segmentLen
  bound : p.blocks * 1024 < 2 ^ 64
  read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 232) 8
  write : Covers [⟨matrix s, p.blocks * 1024⟩] s.wr
  frame : (⟨matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨s.gpr .x19, 272⟩
  length : s.gpr .x20 = BitVec.ofNat 64 p.laneLen

structure Represents (p : Params) (memory : Array Block) (acc : Block) (s : State) : Prop where
  accumulator : blockAt s.mem (matrix s) = acc
  last : ∀ lane < p.lanes,
    blockAt s.mem (Proof.Argon2.matrixCell (matrix s) (Proof.Argon2.lastIndex p lane)) =
      memory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock

theorem Ready.block_cover {p : Params} {s : State} (h : Ready p s) (k : Nat) (active : k < p.blocks) :
    Covers [⟨Proof.Argon2.matrixCell (matrix s) k, 1024⟩] s.wr := by
  have sub : Covers [⟨Proof.Argon2.matrixCell (matrix s) k, 1024⟩] [⟨matrix s, p.blocks * 1024⟩] :=
    Covers.of_sub (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact ⟨⟨matrix s, p.blocks * 1024⟩, by simp, k * 1024, rfl, by change k * 1024 + 1024 ≤ p.blocks * 1024; omega⟩)
  exact fun a n ha => h.write a n (sub a n ha)

theorem Ready.accumulator_cover {p : Params} {s : State} (h : Ready p s) :
    Covers [⟨matrix s, 1024⟩] s.wr := by
  have nonempty := Proof.Argon2.lastIndex_bounds p h.positive h.minimum 0 h.positive
  simpa only [Proof.Argon2.matrixCell, Nat.zero_mul, BitVec.add_zero] using h.block_cover 0 (by omega)

theorem Ready.of_keeps {p : Params} {s t : State} (h : Ready p s)
    (k : Divide.Keeps ReducePointers.changed s t) : Ready p t := by
  have bp := k.regs .x19 (by decide)
  have base : matrix t = matrix s := by unfold matrix; rw [k.mem, bp]
  refine ⟨h.positive, h.minimum, h.bound, ?_, ?_, ?_, (k.regs .x20 (by decide)).trans h.length⟩
  · rw [k.rd, k.wr, bp]; exact h.read
  · rw [base, k.wr]; exact h.write
  · rw [base, bp]; exact h.frame

theorem Represents.of_keeps {p : Params} {s t : State} {memory : Array Block} {acc : Block}
    (h : Represents p memory acc s) (k : Divide.Keeps ReducePointers.changed s t) : Represents p memory acc t := by
  have base : matrix t = matrix s := by unfold matrix; rw [k.mem, k.regs .x19 (by decide)]
  constructor
  · rw [k.mem, base]; exact h.accumulator
  · rw [k.mem, base]; exact h.last

end VG.Proof.Argon2.AArch64.ReductionState
