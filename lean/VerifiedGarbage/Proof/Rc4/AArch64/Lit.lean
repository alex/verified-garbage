import VerifiedGarbage.Impl.Rc4.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Literal code keeps unrolled table scans cheap for kernel-evaluated audits. -/
namespace VG.Impl.Rc4.AArch64
materialize_code lookup
materialize_code replace
materialize_code scheduleStep
materialize_code init
materialize_code applyStep
materialize_code apply
end VG.Impl.Rc4.AArch64
