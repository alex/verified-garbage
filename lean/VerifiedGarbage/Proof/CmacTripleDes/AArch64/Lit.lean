import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.CmacTripleDes.AArch64
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.KeysLit
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.RoundLit

/-! # TDEA-CMAC's AArch64 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.CmacTripleDes.AArch64.init
materialize_code Impl.CmacTripleDes.AArch64.update
materialize_code Impl.CmacTripleDes.AArch64.finalize

end VG
