import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Semantics
import Mathlib.Tactic.IntervalCases

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (C D)

def dreg (x : Nat) : VReg := [VReg.v29, .v30, .v31, .v27, .v28].getD x .v29

def ALanes (σ : Low) (A : Spec.Sha3.State) : Prop :=
  ∀ i (hi : i < 25), σ (vreg i) = A[i]

def DLanes (σ : Low) (A : Spec.Sha3.State) : Prop :=
  ∀ x < 5, σ (dreg x) = D A x

theorem theta_preserves (σ : Low) (r : VReg) (hr : ∀ x < 7, r ≠ vreg (25 + x)) :
    runLow theta σ r = σ r := by
  have h25 := hr 0 (by decide)
  have h26 := hr 1 (by decide)
  have h27 := hr 2 (by decide)
  have h28 := hr 3 (by decide)
  have h29 := hr 4 (by decide)
  have h30 := hr 5 (by decide)
  have h31 := hr 6 (by decide)
  simp only [vreg, List.getD_cons_succ, List.getD_cons_zero] at h25 h26 h27 h28 h29 h30 h31
  simp only [runLow, theta, List.foldl_cons, List.foldl_nil, opLow, put,
    h25, h26, h27, h28, h29, h30, h31, ite_false]

theorem theta_lanes (σ : Low) (A : Spec.Sha3.State) (h : ALanes σ A) :
    ALanes (runLow theta σ) A := by
  intro i hi
  rw [theta_preserves]
  · exact h i hi
  · exact (show ∀ i < 25, ∀ x < 7, vreg i ≠ vreg (25 + x) by decide) i hi

/-- The five correction words use RAX1's rotate-left by one. -/
theorem theta_d (σ : Low) (A : Spec.Sha3.State) (h : ALanes σ A) (x : Nat) (hx : x < 5) :
    runLow theta σ (dreg x) = D A x := by
  have ha : ∀ i (hi : i < 25), σ (vreg i) = A[i]! := fun i hi => (h i hi).trans
    (VG.Proof.Sha3.getElem!_eq A hi).symm
  interval_cases x <;>
    simp only [runLow, theta, List.foldl_cons, List.foldl_nil, opLow, put, dreg,
      List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq, ite_true, ite_false]
  all_goals
    have h0 := ha 0 (by decide)
    have h1 := ha 1 (by decide)
    have h2 := ha 2 (by decide)
    have h3 := ha 3 (by decide)
    have h4 := ha 4 (by decide)
    have h5 := ha 5 (by decide)
    have h6 := ha 6 (by decide)
    have h7 := ha 7 (by decide)
    have h8 := ha 8 (by decide)
    have h9 := ha 9 (by decide)
    have h10 := ha 10 (by decide)
    have h11 := ha 11 (by decide)
    have h12 := ha 12 (by decide)
    have h13 := ha 13 (by decide)
    have h14 := ha 14 (by decide)
    have h15 := ha 15 (by decide)
    have h16 := ha 16 (by decide)
    have h17 := ha 17 (by decide)
    have h18 := ha 18 (by decide)
    have h19 := ha 19 (by decide)
    have h20 := ha 20 (by decide)
    have h21 := ha 21 (by decide)
    have h22 := ha 22 (by decide)
    have h23 := ha 23 (by decide)
    have h24 := ha 24 (by decide)
    simp only [vreg, List.getD_cons_succ, List.getD_cons_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24
    simp only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,
      D, C, VG.Proof.Sha3.rotateLeft_eq _ (by decide : 0 < 1) (by decide : 1 < 64),
      Nat.reduceAdd, Nat.reduceMod]
    rw [BitVec.xor_comm]
    congr 1 <;> ac_rfl

end VG.Proof.Sha3.AArch64.Sha3.Vector
