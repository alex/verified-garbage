import VerifiedGarbage.Proof.Rc2.AArch64.Lit
import VerifiedGarbage.Impl.Rc2.AArch64.Cbc

/-! # Literal CBC callers -/

namespace VG

materialize_code Impl.Rc2.AArch64.Cbc.encrypt
materialize_code Impl.Rc2.AArch64.Cbc.decrypt

end VG
