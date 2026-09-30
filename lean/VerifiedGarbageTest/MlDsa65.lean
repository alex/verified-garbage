import VerifiedGarbageTest.MlDsa

/-!
# Known-answer tests for the ML-DSA specification: ML-DSA-65

The checks of `VerifiedGarbageTest/MlDsa.lean` on the ML-DSA-65 vectors.
-/

/-- The sizes of Table 2. -/
example : VG.Spec.MlDsa.mlDsa65.pkLen = 1952 ∧ VG.Spec.MlDsa.mlDsa65.skLen = 4032 ∧
    VG.Spec.MlDsa.mlDsa65.sigLen = 3309 := by decide +kernel

run_cmd VG.Test.MlDsa.check "ML-DSA-65"
