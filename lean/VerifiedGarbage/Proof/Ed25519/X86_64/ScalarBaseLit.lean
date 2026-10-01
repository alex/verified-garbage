import VerifiedGarbage.Impl.X25519.X86_64.Adx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase

/-! A checked literal for the complete base-point multiplication program. -/

namespace VG

materialize_code scalarBaseLit := (Impl.Ed25519.X86_64.scalarBase Impl.X25519.X86_64.baseline )
materialize_code scalarBaseAdxLit := (Impl.Ed25519.X86_64.scalarBase Impl.X25519.X86_64.adx )

end VG
