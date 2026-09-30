import VerifiedGarbageTest.MlDsa

/-!
# Known-answer tests for the ML-DSA specification: ML-DSA-44

The checks of `VerifiedGarbageTest/MlDsa.lean` on the ML-DSA-44 vectors.
-/

/-- The sizes of Table 2. -/
example : VG.Spec.MlDsa.mlDsa44.pkLen = 1312 ∧ VG.Spec.MlDsa.mlDsa44.skLen = 2560 ∧
    VG.Spec.MlDsa.mlDsa44.sigLen = 2420 := by decide +kernel

run_cmd VG.Test.MlDsa.check "ML-DSA-44"
