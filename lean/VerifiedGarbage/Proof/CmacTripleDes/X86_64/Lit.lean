import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.CmacTripleDes.X86_64
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.KeysLit
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.RoundLit

/-! # TDEA-CMAC's x86-64 code as literals, for kernel-evaluated checks -/

namespace VG

materialize_code Impl.CmacTripleDes.X86_64.init
materialize_code Impl.CmacTripleDes.X86_64.update
materialize_code Impl.CmacTripleDes.X86_64.finalize

end VG
