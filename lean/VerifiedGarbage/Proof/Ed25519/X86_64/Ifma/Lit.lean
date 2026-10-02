import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.Ifma

/-! A checked literal for the doublings with AVX512_IFMA. -/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64

materialize_code double4Lit := (Impl.Ed25519.X86_64.Ifma.double4 : Prog isa)

end VG.Proof.Ed25519.X86_64.Ifma
