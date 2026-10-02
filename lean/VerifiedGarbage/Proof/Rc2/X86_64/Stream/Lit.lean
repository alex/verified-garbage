import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Lit
import VerifiedGarbage.Impl.Rc2.X86_64.Stream

/-! # Literal streaming functions -/

namespace VG

materialize_code Impl.Rc2.X86_64.Stream.init
materialize_code Impl.Rc2.X86_64.Stream.encryptUpdate
materialize_code Impl.Rc2.X86_64.Stream.decryptUpdate

end VG
