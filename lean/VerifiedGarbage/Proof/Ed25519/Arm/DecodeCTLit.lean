import VerifiedGarbage.Impl.Ed25519.Arm.PointDecode
import VerifiedGarbage.Impl.Ed25519.Arm.PointEqual
import VerifiedGarbage.Proof.Framework.Arm.Lit

namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm
materialize_code recoverCandidate
materialize_code pointDecodeLoad
materialize_code recoverSuccess
materialize_code equal116CT := fieldEqual 11 6
materialize_code equal1112CT := fieldEqual 11 12
materialize_code equal89CT := fieldEqual 8 9
materialize_code equal1011CT := fieldEqual 10 11
materialize_code equalOpsCT := fieldCode pointEqualOps
materialize_code zero0CT := fieldZero 0
materialize_code parityCT := (.block (freeze 0 ++ recoverParity) : Prog isa)
materialize_code negateCT := fieldCode [.const 5 0, .sub 0 5 0]
materialize_code rootAdjustCT := fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18]
end VG.Proof.Ed25519.Arm
