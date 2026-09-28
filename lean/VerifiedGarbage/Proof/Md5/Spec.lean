import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Spec.Md5

/-!
# MD5: lemmas about the specification

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Md5

open VG.Spec.Md5

/-! ## Operations -/

/-- Operation `[abcd k s i]` with the auxiliary function of round `r`, the
word `x = X[k]`, the constant `T[i]` and the rotation `s` explicit. -/
def stepKX (v : HashValue) (r : Nat) (x T : Word) (s : Nat) : HashValue :=
  #v[v[3], v[1] + (v[0] + roundFn r v[1] v[2] v[3] + x + T).rotateLeft s, v[1], v[2]]

/-- The index `k` of every operation is a word of the block. -/
theorem ks_lt : ∀ t < 64, ks.getD t 0 < 16 := by decide

/-- The rotation of operation `t`. -/
def rot (t : Nat) : Nat := (ss.getD (t / 16) []).getD (t % 4) 0

theorem rot_range : ∀ t < 64, 1 ≤ rot t ∧ rot t ≤ 31 := by decide

theorem step_eq (X : Block) (v : HashValue) {t : Nat} (ht : t < 64) :
    step X v t = stepKX v (t / 16) (X ⟨ks.getD t 0, ks_lt t ht⟩) (Ts.getD t 0) (rot t) := by
  simp only [step, stepKX, rot, ks_lt t ht, dite_true]

theorem steps_zero (H : HashValue) (X : Block) : steps H X 0 = H := rfl

theorem steps_succ (H : HashValue) (X : Block) (t : Nat) :
    steps H X (t + 1) = step X (steps H X t) t := by
  simp [steps, List.range_succ, List.foldl_append]

/-! ## Bitwise identities used by the implementations -/

theorem F_eq (x y z : Word) : F x y z = (y ^^^ z) &&& x ^^^ z := by
  ext i; simp only [F, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem G_eq (x y z : Word) : G x y z = (x ^^^ y) &&& z ^^^ y := by
  ext i; simp only [G, BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem H_eq (x y z : Word) : H x y z = x ^^^ y ^^^ z := rfl

theorem I_eq (x y z : Word) : I x y z = (z ^^^ 0xffffffff ||| x) ^^^ y := by
  rw [show (0xffffffff : Word) = BitVec.allOnes 32 by decide, BitVec.xor_allOnes]
  ext i; simp only [I, BitVec.getElem_xor, BitVec.getElem_or, BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem rotateLeft_eq (x : Word) {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 31) :
    x.rotateLeft n = x.rotateRight (32 - n) := by
  ext i hi
  simp only [BitVec.getElem_rotateLeft, BitVec.getElem_rotateRight]
  split_ifs <;> first | omega | (congr 1; omega)

end VG.Proof.Md5
