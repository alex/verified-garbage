import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.CmacTripleDes.X86

/-! # TDEA-CMAC's x86 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.CmacTripleDes.X86.init
materialize_code Impl.CmacTripleDes.X86.update
materialize_code Impl.CmacTripleDes.X86.finalize

end VG
