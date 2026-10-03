import VerifiedGarbage.Impl.Ed25519.Arm.ScalarBase
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Ed25519.Arm.Field
import VerifiedGarbage.Impl.Ed25519.Arm.Power

/-! The point arithmetic and the inversion chain as literals
(`materialize_value`, `materialize_code`), which the literals of the code
that contains them read rather than build each field multiplication again. -/
namespace VG.Impl.Ed25519.Arm

materialize_code pointAdd
materialize_code pointDouble
materialize_code power250
materialize_code invert
materialize_code rootPower

end VG.Impl.Ed25519.Arm

namespace VG.Impl.Ed25519.Arm
materialize_code prepareBatch
materialize_code accumulate16
materialize_code pointEncode
materialize_code powers32CT := pointPowers 1600 32 true
materialize_code powers16CT := pointPowers 1600 16 true
materialize_code identityCT := constPoint Spec.Ed25519.identity
materialize_code basePointCT := constPoint Spec.Ed25519.basePoint
end VG.Impl.Ed25519.Arm
