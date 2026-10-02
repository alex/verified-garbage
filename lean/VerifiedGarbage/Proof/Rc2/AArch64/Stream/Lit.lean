import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Lit
import VerifiedGarbage.Impl.Rc2.AArch64.Stream

/-! # Literal streaming RC2-CBC programs

`init` and the update functions as literals (`materialize_code`), whose calls
refer to the literals of the key expansion and the CBC functions. -/

namespace VG

materialize_code Impl.Rc2.AArch64.Stream.init
materialize_code Impl.Rc2.AArch64.Stream.encryptUpdate
materialize_code Impl.Rc2.AArch64.Stream.decryptUpdate

end VG
