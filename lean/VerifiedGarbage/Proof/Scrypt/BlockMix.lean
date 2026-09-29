import VerifiedGarbage.Spec.Scrypt
import Mathlib.Tactic.Ring.RingNF

/-!
# scryptBlockMix, one block at a time

Untrusted: everything here is checked by Lean. `blockMix` in the order an
implementation computes it: `Y[i]` from the previous one (`yAt`), and the
output as the blocks `Y[0], Y[2], …` followed by `Y[1], Y[3], …`.
-/

namespace VG.Proof.Scrypt

open VG.Spec.Scrypt
open VG.Spec.Pbkdf2 (xorBytes)

variable (b : List Byte) (r : Nat)

/-- `Y[i]`. -/
def yAt : Nat → List Byte
  | 0 => salsa (xorBytes (blk b (2 * r - 1)) (blk b 0))
  | i + 1 => salsa (xorBytes (yAt i) (blk b (i + 1)))

/-- `X` before step `i` of scryptBlockMix's step 2. -/
def xBefore : Nat → List Byte
  | 0 => blk b (2 * r - 1)
  | i + 1 => yAt b r i

theorem yAt_eq (i : Nat) : yAt b r i = salsa (xorBytes (xBefore b r i) (blk b i)) := by
  cases i <;> rfl

theorem xBefore_succ (i : Nat) : xBefore b r (i + 1) = yAt b r i := rfl

theorem blockMixYs_range' (n : Nat) : ∀ s,
    blockMixYs b (xBefore b r s) (List.range' s n) = (List.range' s n).map (yAt b r) := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    simp only [List.range'_succ, List.map_cons, blockMixYs]
    rw [← yAt_eq, ← xBefore_succ, ih (s + 1)]

theorem blockMixYs_range (n : Nat) :
    blockMixYs b (blk b (2 * r - 1)) (List.range n) = (List.range n).map (yAt b r) := by
  rw [List.range_eq_range']
  exact blockMixYs_range' b r n 0

theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- scryptBlockMix as the even-indexed `Y[i]` followed by the odd-indexed ones. -/
theorem blockMix_eq : blockMix r b =
    ((List.range r).flatMap fun i => yAt b r (2 * i)) ++
      ((List.range r).flatMap fun i => yAt b r (2 * i + 1)) := by
  simp only [blockMix, blockMixYs_range]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]; rfl
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]; rfl

theorem length_flatMap_const {α β : Type} (l : List α) {f : α → List β} {n : Nat}
    (h : ∀ a, (f a).length = n) : (l.flatMap f).length = n * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, h, ih, List.length_cons]; ring

theorem serialize_length (x : Vector Word 16) : (serialize x).length = 64 := by
  rw [serialize, length_flatMap_const _ (n := 4) fun _ => rfl]; simp

theorem salsa_length (t : List Byte) : (salsa t).length = 64 := serialize_length _

theorem yAt_length (i : Nat) : (yAt b r i).length = 64 := by
  rw [yAt_eq]; exact salsa_length _

end VG.Proof.Scrypt
