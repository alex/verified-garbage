import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Stages

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

def iotaFile (f : File) (rc : Lane) : File :=
  f.write .x0 (f.regs .x0 ^^^ rc)

theorem laneReg_zero : ∀ i < 25, laneReg i = .x0 ↔ i = 0 := by decide +kernel

theorem iota_correct (A : Spec.Sha3.State) (f : File) (h : Holds laneReg A f)
    (ir : Nat) : Holds laneReg (Spec.Sha3.iota A ir) (iotaFile f (Spec.Sha3.RC ir)) := by
  intro i hi
  by_cases hz : i = 0
  · subst i
    simp only [iotaFile, File.write, laneReg, ↓reduceIte, Spec.Sha3.iota,
      Vector.getElem_set_self]
    exact congrArg (· ^^^ Spec.Sha3.RC ir) (h 0 (by decide))
  · have hr : laneReg i ≠ .x0 := by
      intro hr; exact hz ((laneReg_zero i hi).mp hr)
    simp only [iotaFile, File.write, hr, ↓reduceIte, h i hi, Spec.Sha3.iota,
      Vector.getElem_set, Ne.symm hz]

@[irreducible] def roundFile (f : File) (rc : Lane) : File :=
  iotaFile (run chiOps (run rhoPiOps (run thetaOps f))) rc

theorem round_correct (A : Spec.Sha3.State) (f : File) (h : Holds laneReg A f)
    (ir : Nat) : Holds laneReg (Spec.Sha3.rnd A ir) (roundFile f (Spec.Sha3.RC ir)) := by
  unfold roundFile
  exact iota_correct _ _ (chi_correct _ _ (rhoPi_correct _ _ (theta_correct A f h))) ir

theorem rounds_correct (irs : List Nat) (A : Spec.Sha3.State) (f : File)
    (h : Holds laneReg A f) :
    Holds laneReg (irs.foldl Spec.Sha3.rnd A)
      (irs.foldl (fun f ir => roundFile f (Spec.Sha3.RC ir)) f) := by
  induction irs generalizing A f with
  | nil => exact h
  | cons ir irs ih =>
    simp only [List.foldl_cons]
    have hn := round_correct A f h ir
    exact ih (Spec.Sha3.rnd A ir) (roundFile f (Spec.Sha3.RC ir)) hn

theorem keccakF_correct (A : Spec.Sha3.State) (f : File) (h : Holds laneReg A f) :
    Holds laneReg (Spec.Sha3.keccakF A)
      ((List.range 24).foldl (fun f ir => roundFile f (Spec.Sha3.RC ir)) f) :=
  rounds_correct (List.range 24) A f h

end VG.Proof.Sha3.AArch64.Scalar
