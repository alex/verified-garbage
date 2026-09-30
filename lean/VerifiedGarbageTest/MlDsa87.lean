import VerifiedGarbageTest.MlDsa

/-!
# Known-answer tests for the ML-DSA specification: ML-DSA-87

The checks of `VerifiedGarbageTest/MlDsa.lean` on the ML-DSA-87 vectors.
-/

/-- The sizes of Table 2. -/
example : VG.Spec.MlDsa.mlDsa87.pkLen = 2592 ∧ VG.Spec.MlDsa.mlDsa87.skLen = 4896 ∧
    VG.Spec.MlDsa.mlDsa87.sigLen = 4627 := by decide +kernel

run_cmd VG.Test.MlDsa.check "ML-DSA-87"
