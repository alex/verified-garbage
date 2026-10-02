import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix

/-!
# scrypt on X86_64: the code as literals
-/

namespace VG

materialize_code Impl.Scrypt.X86_64.salsa
materialize_code Impl.Scrypt.X86_64.blockMix
materialize_code Impl.Scrypt.X86_64.roMix

end VG
