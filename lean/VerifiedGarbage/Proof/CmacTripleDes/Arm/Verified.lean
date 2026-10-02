import VerifiedGarbage.Proof.CmacTripleDes.Arm.FinalizeCorrect
import VerifiedGarbage.Proof.CmacTripleDes.Arm.CT
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Implies

/-!
# TDEA-CMAC on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time under this target's contracts (`Contract.lean`), and the shared
contracts of `Spec/Cmac/TripleDesContract.lean`, which imply them, with no
stack: the functions call nothing, and save our caller's registers in the
scratch buffer.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm

theorem init_verified : Verified Arm.target init (Spec.Cmac.tdesInitContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct init_implies

theorem update_verified : Verified Arm.target update (Spec.Cmac.tdesUpdateContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => update_wp hs) update_ct update_implies

theorem finalize_verified : Verified Arm.target finalize (Spec.Cmac.tdesFinalizeContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => finalize_wp hs) finalize_ct finalize_implies

end VG.Proof.CmacTripleDes.Arm
