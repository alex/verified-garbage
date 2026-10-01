import VerifiedGarbage.Impl.Ed25519.Arm.ScalarBase
import VerifiedGarbage.Proof.Framework.Arm.Lit

namespace VG.Impl.Ed25519.Arm
materialize_code prepareBatch
materialize_code accumulate16
materialize_code pointEncode
materialize_code powers32CT := pointPowers 1600 32 true
materialize_code powers16CT := pointPowers 1600 16 true
materialize_code identityCT := constPoint Spec.Ed25519.identity
materialize_code basePointCT := constPoint Spec.Ed25519.basePoint
end VG.Impl.Ed25519.Arm
