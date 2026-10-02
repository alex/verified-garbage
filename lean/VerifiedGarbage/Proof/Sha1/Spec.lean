import VerifiedGarbage.Spec.Sha1
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# SHA-1: lemmas about the specification
-/

namespace VG.Proof.Sha1

open VG.Spec.Sha1

/-! ## The message schedule -/

theorem schedule_succ (M : Block) (t : Nat) : schedule M (t + 1) = W M t :: schedule M t := rfl

theorem schedule_length (M : Block) (t : Nat) : (schedule M t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [schedule_succ, List.length_cons, ih]

theorem schedule_getElem! (M : Block) {t i : Nat} (hi : i < t) :
    (schedule M t)[i]! = W M (t - 1 - i) := by
  induction t generalizing i with
  | zero => omega
  | succ t ih =>
    rw [schedule_succ]
    cases i with
    | zero => simp
    | succ i =>
      simp only [getElem!_pos (W M t :: schedule M t) (i + 1) (by
          simp only [List.length_cons, schedule_length]; omega),
        List.getElem_cons_succ]
      rw [← getElem!_pos, ih (by omega)]
      congr 1; omega

theorem W_lt (M : Block) {t : Nat} (h : t < 16) : W M t = M ⟨t, h⟩ := by
  simp [W, schedule, h]

theorem W_ge (M : Block) {t : Nat} (h : 16 ≤ t) :
    W M t = (W M (t - 3) ^^^ W M (t - 8) ^^^ W M (t - 14) ^^^ W M (t - 16)).rotateLeft 1 := by
  show (schedule M (t + 1)).headD 0 = _
  simp only [schedule, show ¬ t < 16 by omega, dite_false, List.headD_cons]
  rw [schedule_getElem! M (by omega), schedule_getElem! M (by omega),
    schedule_getElem! M (by omega), schedule_getElem! M (by omega),
    show t - 1 - 2 = t - 3 by omega, show t - 1 - 7 = t - 8 by omega,
    show t - 1 - 13 = t - 14 by omega, show t - 1 - 15 = t - 16 by omega]

/-! ## Rounds -/

/-- One round with explicit `fₜ(b, c, d)`, `Kₜ` and `Wₜ`. -/
def roundKW (v : HashValue) (fv k w : Word) : HashValue :=
  #v[v[0].rotateLeft 5 + fv + v[4] + k + w, v[0], v[1].rotateLeft 30, v[2], v[3]]

theorem round_eq (M : Block) (v : HashValue) (t : Nat) :
    round M v t = roundKW v (f t v[1] v[2] v[3]) (K t) (W M t) := rfl

theorem rounds_zero (H : HashValue) (M : Block) : rounds H M 0 = H := rfl

theorem rounds_succ (H : HashValue) (M : Block) (t : Nat) :
    rounds H M (t + 1) = round M (rounds H M t) t := by
  simp [rounds, List.range_succ, List.foldl_append]

/-! ## Bitwise identities used by the implementations -/

/-- `ROTLⁿ` is a rotation right by `32 - n`. -/
theorem rotateLeft_eq (x : Word) {n : Nat} (h : n < 32) :
    x.rotateLeft n = x.rotateRight (32 - n) := by
  ext i hi
  simp only [BitVec.getElem_rotateLeft, BitVec.getElem_rotateRight]
  split_ifs <;> first | omega | (congr 1; omega)

theorem ch_eq (x y z : Word) : ch x y z = (y ^^^ z) &&& x ^^^ z := by
  ext i; simp only [ch, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem maj_eq (x y z : Word) : maj x y z = (x ||| y) &&& z ||| x &&& y := by
  ext i; simp only [maj, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

end VG.Proof.Sha1
