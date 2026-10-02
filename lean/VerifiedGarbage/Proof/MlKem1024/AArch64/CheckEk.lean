import VerifiedGarbage.Proof.MlKem.AArch64.CheckEk
import VerifiedGarbage.Impl.MlKem1024.AArch64.CheckEk

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_check_ek`

ML-KEM-768's proof (`Proof/MlKem/AArch64/CheckEk.lean`), which is stated for
`k ≤ 4`, for ML-KEM-1024 (the 512 groups of `ek[0 : 1536]`).
-/

namespace VG.Proof.MlKem1024.AArch64.CheckEk

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.CheckEk (correct)
open VG.Spec.MlKem (Params mlKem1024)

theorem ct : ConstantTime isa (checkEkAArch64 mlKem1024).pre (checkEkAArch64 mlKem1024).pub checkEk :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ ⟨h0, hsp⟩ => agree_of hsp (by simp [h0])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1568⟩]
  wr := []

theorem checkEk_verified : Verified AArch64.target checkEk (Spec.MlKem1024.checkEkContract AArch64.abi) :=
  Verified.of_correct (correct (p := mlKem1024) ⟨by decide, by decide⟩) ct (by
    mlkem_implies [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, checkEkAArch64,
      Spec.MlKem.mlKem1024, Params.ekLen, AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem1024.AArch64.CheckEk
