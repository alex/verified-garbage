import VerifiedGarbage.Impl.Rc4.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! Literal code keeps unrolled table scans cheap for kernel-evaluated audits. -/
namespace VG.Impl.Rc4.X86_64
materialize_value lookup
materialize_value replace
materialize_value scheduleStep
materialize_value applyStep
materialize_code init
materialize_code apply
end VG.Impl.Rc4.X86_64
