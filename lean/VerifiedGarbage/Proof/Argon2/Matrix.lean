import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-! Relate the lane-major assembly allocation to the specification's block array. -/

namespace VG.Proof.Argon2

open VG VG.Spec.Argon2

def matrixCell (base : Addr) (k : Nat) : Addr := base + BitVec.ofNat 64 (k * 1024)

structure Represents (m : Mem) (base : Addr) (n : Nat) (blocks : Array Block) : Prop where
  size : blocks.size = n
  block : ∀ k < n, blockAt m (matrixCell base k) = blocks[k]?.getD zeroBlock

theorem Represents.update {m m' : Mem} {base : Addr} {n : Nat} {blocks : Array Block}
    (h : Represents m base n blocks) (k : Nat) (hk : k < n) (value : Block)
    (written : blockAt m' (matrixCell base k) = value)
    (kept : ∀ j < n, j ≠ k → blockAt m' (matrixCell base j) = blockAt m (matrixCell base j)) :
    Represents m' base n (blocks.set! k value) := by
  refine ⟨(Array.size_set! _ _ _).trans h.size, ?_⟩
  intro j hj
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases equal : k = j
  · rw [ite_eq_left equal, ite_eq_left (by rw [h.size]; exact hk), Option.getD_some]
    rw [← equal]; exact written
  · rw [ite_eq_right equal]
    exact (kept j hj (Ne.symm equal)).trans (h.block j hj)

theorem matrixCell_sub (base : Addr) (n k : Nat) (hk : k < n) :
    Region.Sub ⟨matrixCell base k, 1024⟩ ⟨base, n * 1024⟩ :=
  Offset.sub_base base (by omega)

theorem matrixCell_disjoint (base : Addr) (n i j : Nat) (bound : n * 1024 < 2 ^ 64)
    (hi : i < n) (hj : j < n) (different : i ≠ j) :
    (⟨matrixCell base i, 1024⟩ : Region).Disjoint ⟨matrixCell base j, 1024⟩ :=
  Offset.disjoint base (by omega) (by omega) (by omega)

end VG.Proof.Argon2
