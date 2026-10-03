import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.CmacTripleDes.Arm
import VerifiedGarbage.Proof.CmacTripleDes.Arm.KeysLit
import VerifiedGarbage.Proof.CmacTripleDes.Arm.RoundLit

/-! # TDEA-CMAC's ARMv7 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.CmacTripleDes.Arm.init
materialize_code Impl.CmacTripleDes.Arm.update
materialize_code Impl.CmacTripleDes.Arm.finalize

end VG
