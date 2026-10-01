import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Rc2.X86_64.Block
import VerifiedGarbage.Impl.Rc2.X86_64.ExpandKey

/-! # Literal RC2 programs for kernel-evaluated checks -/

namespace VG

materialize_code Impl.Rc2.X86_64.encryptBlock
materialize_code Impl.Rc2.X86_64.decryptBlock
materialize_code Impl.Rc2.X86_64.expandKey

end VG
