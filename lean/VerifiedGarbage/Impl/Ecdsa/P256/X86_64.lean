import VerifiedGarbage.Impl.Ecdsa.X86_64
import VerifiedGarbage.Spec.P256

/-! # ECDSA over P-256 on x86-64: four-word field elements and scalars -/

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

/-- P-256 as the code has it. -/
def p256 : Cfg := ⟨4, Spec.P256.curve⟩

/-- `vg_ecdsa_p256_sign`. -/
def signP256 : Prog isa := p256.sign

end VG.Impl.Ecdsa.X86_64
