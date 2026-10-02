import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Scrypt.Arm.RoMix

/-!
# scrypt on Arm: the code as literals
-/

namespace VG

materialize_code Impl.Scrypt.Arm.salsa
materialize_code Impl.Scrypt.Arm.blockMix
materialize_code Impl.Scrypt.Arm.roMix

end VG
