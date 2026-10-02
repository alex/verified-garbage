import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Argon2.Dimensions

/-! The final lane reduction, without changing the reviewed finish specification. -/

namespace VG.Proof.Argon2

open VG VG.Spec.Argon2

def lastIndex (p : Params) (lane : Nat) : Nat := (lane + 1) * p.laneLen - 1

def reduction (p : Params) (memory : Array Block) (start count : Nat) (acc : Block) : Block :=
  (List.range' start count).foldl (fun b lane => xorBlock b (memory[lastIndex p lane]?.getD zeroBlock)) acc

theorem reduction_zero (p : Params) (memory : Array Block) (start : Nat) (acc : Block) :
    reduction p memory start 0 acc = acc := rfl

theorem reduction_succ (p : Params) (memory : Array Block) (start count : Nat) (acc : Block) :
    reduction p memory start (count + 1) acc =
      reduction p memory (start + 1) count (xorBlock acc (memory[lastIndex p start]?.getD zeroBlock)) := by
  simp only [reduction, List.range'_succ, List.foldl_cons]

theorem finish_reduction (p : Params) (memory : Array Block) :
    finish p memory = hPrime p.tagLen (serialize (reduction p memory 0 p.lanes zeroBlock)) := by
  rw [finish, reduction, List.range_eq_range']
  rfl

theorem lastIndex_bounds (p : Params) (positive : 0 < p.lanes) (minimum : 2 ≤ p.segmentLen)
    (lane : Nat) (active : lane < p.lanes) : 0 < lastIndex p lane ∧ lastIndex p lane < p.blocks := by
  have q : 8 ≤ p.laneLen := by
    have eq := laneLen_segments p positive
    omega
  have total := blocks_lanes p positive
  have product : (lane + 1) * p.laneLen ≤ p.lanes * p.laneLen := Nat.mul_le_mul_right _ (by omega)
  have low : p.laneLen ≤ (lane + 1) * p.laneLen := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right p.laneLen (show 1 ≤ lane + 1 by omega)
  unfold lastIndex
  omega

theorem xorBlock_comm (a b : Block) : xorBlock a b = xorBlock b a := by
  apply Vector.ext
  intro i hi
  simp only [xorBlock, Vector.getElem_zipWith, BitVec.xor_comm]

end VG.Proof.Argon2
