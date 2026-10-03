import VerifiedGarbage.Impl.Rc4.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Literal code keeps the unrolled groups cheap for kernel-evaluated audits. -/
namespace VG.Impl.Rc4.AArch64
materialize_code applyRest
materialize_code apply
materialize_code init
end VG.Impl.Rc4.AArch64
