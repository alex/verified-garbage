import VerifiedGarbageTest.MlKem

/-!
# Known-answer tests for the ML-KEM specification: ML-KEM-512

The checks of `VerifiedGarbageTest/MlKem.lean` on the ML-KEM-512 vectors.
-/

run_cmd VG.Test.MlKem.check "ML-KEM-512" (all := false)
