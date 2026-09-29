import VerifiedGarbageTest.MlKem
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# Known-answer tests for the ML-KEM specification: ML-KEM-1024

The checks of `VerifiedGarbageTest/MlKem.lean` on the ML-KEM-1024 vectors:
all of them, as ML-KEM-1024 has contracts (`Spec/MlKem/Contract1024.lean`).
-/

/-- The sizes of Table 3, which the contracts of ML-KEM-1024 write as
literals. -/
example : VG.Spec.MlKem.mlKem1024.ekLen = 1568 ∧ VG.Spec.MlKem.mlKem1024.dkLen = 3168 ∧
    VG.Spec.MlKem.mlKem1024.ctLen = 1568 := by decide

run_cmd VG.Test.MlKem.check "ML-KEM-1024" (all := true)
