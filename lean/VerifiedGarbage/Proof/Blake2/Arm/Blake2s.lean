import VerifiedGarbage.Proof.Blake2.Arm.CompressS.Compress
import VerifiedGarbage.Proof.Blake2.Arm.Stream.Verified

/-!
# BLAKE2s on ARMv7: the streaming functions

Untrusted: everything here is checked by Lean. The streaming layer
(`Proof/Blake2/Arm/Stream/`) instantiated with BLAKE2s and its compression
function (`Proof/Blake2/Arm/CompressS/`), against the shared contracts of
`Spec/Blake2/Contract.lean`.
-/

namespace VG.Proof.Blake2.Arm.Blake2s

open VG VG.Arm
open VG.Proof.Blake2.Arm.Stream

theorem calleeS : CalleeOk Spec.Blake2.s Impl.Blake2.Arm.S.compress :=
  ⟨Proof.Blake2.ArmS.compress_verified', Proof.Blake2.ArmS.compress_noCalls⟩

theorem initS_verified :
    Verified Arm.target (Impl.Blake2.Arm.Stream.init Spec.Blake2.s) (Spec.Blake2.initSContract Arm.abi) :=
  init_verified okS init_check_s initS_implies

theorem updateS_verified :
    Verified Arm.target
      (Impl.Blake2.Arm.Stream.update (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)
      (Spec.Blake2.updateSContract Arm.abi 16) :=
  update_verified okS calleeS updateS_implies

theorem finalizeS_verified :
    Verified Arm.target
      (Impl.Blake2.Arm.Stream.finalize (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)
      (Spec.Blake2.finalizeSContract Arm.abi 16) :=
  finalize_verified okS calleeS finalizeS_implies

end VG.Proof.Blake2.Arm.Blake2s
