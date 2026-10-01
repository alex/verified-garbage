import VerifiedGarbage.Proof.ChaCha20.Spec
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Fin.Basic

namespace VG.Proof.ChaCha20.AArch64.Neon

open VG.Spec.ChaCha20 (quarterRound qround innerBlock)

def columns (v : CState) : CState :=
  qround (qround (qround (qround v 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15

def align (v : CState) : CState := Vector.ofFn fun i =>
  v[4 * (i.val / 4) + (i.val % 4 + i.val / 4) % 4]'(by omega)

def unalign (v : CState) : CState := Vector.ofFn fun i =>
  v[4 * (i.val / 4) + (i.val % 4 + 4 - i.val / 4) % 4]'(by omega)

theorem columns_get (v : CState) (e : Nat) (he : e < 4) :
    let q := quarterRound v[e] v[4 + e] v[8 + e] v[12 + e]
    (columns v)[e] = q.1 ∧ (columns v)[4 + e] = q.2.1 ∧
      (columns v)[8 + e] = q.2.2.1 ∧ (columns v)[12 + e] = q.2.2.2 := by
  interval_cases e <;> simp (config := {decide := true}) only [columns, qround_get, Fin.getElem_fin, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, ite_true, ite_false, and_self]

theorem align_get (v : CState) (i : Nat) (hi : i < 16) :
    (align v)[i] = v[4 * (i / 4) + (i % 4 + i / 4) % 4]'(by omega) := by
  simp only [align, Vector.getElem_ofFn]

theorem unalign_get (v : CState) (i : Nat) (hi : i < 16) :
    (unalign v)[i] = v[4 * (i / 4) + (i % 4 + 4 - i / 4) % 4]'(by omega) := by
  simp only [unalign, Vector.getElem_ofFn]

def diagonals (v : CState) : CState :=
  qround (qround (qround (qround v 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14

theorem diagonal_eq (v : CState) : unalign (columns (align v)) = diagonals v := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp (config := {decide := true}) only [unalign_get, align_get, columns, diagonals, qround_get, Fin.getElem_fin, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, ite_true, ite_false]

theorem innerBlock_eq (v : CState) :
    unalign (columns (align (columns v))) = innerBlock v := by
  rw [diagonal_eq]
  rfl

end VG.Proof.ChaCha20.AArch64.Neon
