import VerifiedGarbageTest.MlKem

/-!
# Known-answer tests for the ML-KEM specification: ML-KEM-1024

The checks of `VerifiedGarbageTest/MlKem.lean` on the ML-KEM-1024 vectors.
-/

run_cmd VG.Test.MlKem.check "ML-KEM-1024" (all := false)
