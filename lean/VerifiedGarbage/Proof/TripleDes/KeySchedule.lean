import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.Framework.Mem

namespace VG.Proof.TripleDes

open VG.Spec.TripleDes

abbrev KeyState := BitVec 28 × BitVec 28 × DesSchedule

def keyStep (state : KeyState) (j : Nat) : KeyState :=
  let c := state.1.rotateLeft (rotations.getD j 0)
  let d := state.2.1.rotateLeft (rotations.getD j 0)
  (c, d, state.2.2.set! j (permute pc2 (c ++ d)))

def keyInitial (key : BitVec 64) : KeyState :=
  let selected := permute pc1 key
  ((selected >>> 28).setWidth 28, selected.setWidth 28, Vector.replicate 16 0)

def keyPrefix (key : BitVec 64) (n : Nat) : KeyState :=
  (List.range n).foldl keyStep (keyInitial key)

theorem keyPrefix_zero (key : BitVec 64) : keyPrefix key 0 = keyInitial key := rfl

theorem keyPrefix_succ (key : BitVec 64) (n : Nat) :
    keyPrefix key (n + 1) = keyStep (keyPrefix key n) n := by
  simp only [keyPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem expandDesKey_prefix (key : BitVec 64) : expandDesKey key = (keyPrefix key 16).2.2 := by
  simp only [expandDesKey, List.forIn_pure_yield_eq_foldl]
  rfl

theorem rotation_value : ∀ j < 16,
    rotations.getD j 0 = if j < 2 ∨ j = 8 ∨ j = 15 then 1 else 2 := by decide

end VG.Proof.TripleDes
