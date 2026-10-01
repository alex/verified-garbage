import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Theta

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Impl.Sha3 (rhoOff piSrc)
open VG.Proof.Sha3 (B rotl)

def BLanes (σ : Low) (A : Spec.Sha3.State) : Prop :=
  ∀ i < 25, σ (breg i) = B A (i % 5) (i / 5)

theorem rho_lanes (σ : Low) (A : Spec.Sha3.State) (hA : ALanes σ A) (hD : DLanes σ A) :
    BLanes (runLow rhoPi σ) A := by
  have ha : ∀ i (hi : i < 25), σ (vreg i) = A[i]! := fun i hi => (hA i hi).trans
    (VG.Proof.Sha3.getElem!_eq A hi).symm
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  have a4 := ha 4 (by decide)
  have a5 := ha 5 (by decide)
  have a6 := ha 6 (by decide)
  have a7 := ha 7 (by decide)
  have a8 := ha 8 (by decide)
  have a9 := ha 9 (by decide)
  have a10 := ha 10 (by decide)
  have a11 := ha 11 (by decide)
  have a12 := ha 12 (by decide)
  have a13 := ha 13 (by decide)
  have a14 := ha 14 (by decide)
  have a15 := ha 15 (by decide)
  have a16 := ha 16 (by decide)
  have a17 := ha 17 (by decide)
  have a18 := ha 18 (by decide)
  have a19 := ha 19 (by decide)
  have a20 := ha 20 (by decide)
  have a21 := ha 21 (by decide)
  have a22 := ha 22 (by decide)
  have a23 := ha 23 (by decide)
  have a24 := ha 24 (by decide)
  simp only [vreg, List.getD_cons_succ, List.getD_cons_zero] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
  have d0 := hD 0 (by decide)
  have d1 := hD 1 (by decide)
  have d2 := hD 2 (by decide)
  have d3 := hD 3 (by decide)
  have d4 := hD 4 (by decide)
  simp only [dreg, List.getD_cons_succ, List.getD_cons_zero] at d0 d1 d2 d3 d4
  intro i hi
  interval_cases i <;>
    simp only [runLow, rhoPi, List.foldl_cons, List.foldl_nil, opLow, put, breg,
      List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq, ite_true, ite_false,
      a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, d0,d1,d2,d3,d4,
      B, piSrc, rhoOff, rotl, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul,
      Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq, ite_true, ite_false]

end VG.Proof.Sha3.AArch64.Sha3.Vector
