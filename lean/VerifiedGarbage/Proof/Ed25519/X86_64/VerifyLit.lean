import VerifiedGarbage.Impl.X25519.X86_64.Adx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
import VerifiedGarbage.Impl.Ed25519.X86_64.Ifma

/-! A checked literal for the complete verification program. -/

namespace VG

materialize_code verifyEquationLit := (Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.baseline
  (Impl.Ed25519.X86_64.double4 Impl.X25519.X86_64.baseline))
materialize_code verifyEquationAdxLit := (Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.adx
  (Impl.Ed25519.X86_64.double4 Impl.X25519.X86_64.adx))
materialize_code verifyEquationIfmaLit := (Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.adx
  Impl.Ed25519.X86_64.Ifma.double4)

end VG
