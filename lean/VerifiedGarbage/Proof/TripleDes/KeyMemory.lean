import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Bytes

namespace VG.Proof.TripleDes

open VG VG.Spec.TripleDes

def componentOffset (n c : Nat) : Nat := if c = 2 ∧ n = 16 then 0 else 8 * c

def componentKeys (m : Mem) (p : Addr) (n c : Nat) : DesSchedule :=
  expandDesKey (decodeBlock (blockAt m (p + BitVec.ofNat 64 (componentOffset n c))))

def expandedMemory (m : Mem) (p : Addr) (n : Nat) : Schedule :=
  Vector.ofFn fun i => ((if i.val < 16 then componentKeys m p n 0 else
    if i.val < 32 then componentKeys m p n 1 else componentKeys m p n 2).getD (i.val % 16) 0).setWidth 64

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

theorem bytesAt_getD (m : Mem) (p : Addr) (n i : Nat) (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]

theorem bytesAt_component (m : Mem) (p : Addr) (n offset : Nat) (hi : offset + 8 ≤ n) :
    (Vector.ofFn fun j : Fin 8 => (bytesAt m p n).getD (offset + j.val) 0) =
      blockAt m (p + BitVec.ofNat 64 offset) := by
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, blockAt]
  rw [bytesAt_getD m p n _ (by omega), Offset.add_ofNat_add_ofNat]

theorem componentOffset_bound (n c : Nat) (hn : validKey n) (hc : c < 3) :
    componentOffset n c + 8 ≤ n := by
  rcases hn with rfl | rfl <;> unfold componentOffset
  · by_cases h : c = 2
    · rw [ite_eq_left (by simp only [h, and_self])]; decide
    · rw [ite_eq_right (by simp only [h, false_and, not_false_eq_true])]; omega
  · rw [ite_eq_right (by simp only [show ¬(24 : Nat) = 16 by decide, and_false, not_false_eq_true])]
    omega

theorem expandKey_memory (m : Mem) (p : Addr) (n : Nat) (hn : validKey n) :
    expandKey (bytesAt m p n) = expandedMemory m p n := by
  have component (c : Nat) (hc : c < 3) :
      expandDesKey (decodeBlock (Vector.ofFn fun j : Fin 8 =>
        (bytesAt m p n).getD ((if c = 2 ∧ (bytesAt m p n).length = 16 then 0 else 8 * c) + j.val) 0)) =
        componentKeys m p n c := by
    rw [bytesAt_length]
    unfold componentKeys
    exact congrArg (fun b => expandDesKey (decodeBlock b))
      (bytesAt_component m p n (componentOffset n c) (componentOffset_bound n c hn hc))
  have third := component 2 (by decide)
  simp only [true_and] at third
  apply Vector.ext
  intro i hi
  simp only [expandKey, expandedMemory, Vector.getElem_ofFn,
    component 0 (by decide), component 1 (by decide)]
  simp only [true_and, third]

end VG.Proof.TripleDes
