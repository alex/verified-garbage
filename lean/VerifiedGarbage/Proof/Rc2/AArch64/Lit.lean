import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Rc2.AArch64.Block
import VerifiedGarbage.Impl.Rc2.AArch64.ExpandKey

/-! # Literal RC2 programs for kernel-evaluated checks -/

namespace VG

materialize_code Impl.Rc2.AArch64.encryptBlock
materialize_code Impl.Rc2.AArch64.decryptBlock

materialize_code Impl.Rc2.AArch64.expandKey

end VG
