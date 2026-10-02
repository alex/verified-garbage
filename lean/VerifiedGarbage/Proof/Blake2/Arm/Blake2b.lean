import VerifiedGarbage.Proof.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Blake2.Arm.Stream.Verified
import VerifiedGarbage.Impl.Blake2.Arm.Stream

/-!
# BLAKE2b on ARMv7: the streaming functions

The generic ARMv7 streaming layer (`Proof/Blake2/Arm/Stream/`) instantiated
with BLAKE2b's parameters and its compression function (`compress_verified'`).
-/

namespace VG.Proof.Blake2.ArmB

open VG VG.Arm
open VG.Proof.Blake2.Arm.Stream (CalleeOk okB init_check_b init_verified update_verified
  finalize_verified initB_implies updateB_implies finalizeB_implies)

theorem calleeB : CalleeOk Spec.Blake2.b Impl.Blake2.Arm.B.compress :=
  ⟨compress_verified', by lit_decide⟩

theorem initB_verified :
    Verified Arm.target (Impl.Blake2.Arm.Stream.init Spec.Blake2.b) (Spec.Blake2.initBContract Arm.abi) :=
  init_verified okB init_check_b initB_implies

theorem updateB_verified :
    Verified Arm.target
      (Impl.Blake2.Arm.Stream.update (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)
      (Spec.Blake2.updateBContract Arm.abi 16) :=
  update_verified okB calleeB updateB_implies

theorem finalizeB_verified :
    Verified Arm.target
      (Impl.Blake2.Arm.Stream.finalize (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)
      (Spec.Blake2.finalizeBContract Arm.abi 16) :=
  finalize_verified okB calleeB finalizeB_implies

end VG.Proof.Blake2.ArmB
