import VerifiedGarbage.Impl.Rc2.X86.Stream
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.X86.KeyLit

/-! # Streaming RC2-CBC on x86 (32-bit): the code as literals -/

namespace VG.Impl.Rc2.X86.Stream
materialize_code init
materialize_code encryptUpdate
materialize_code decryptUpdate
end VG.Impl.Rc2.X86.Stream
