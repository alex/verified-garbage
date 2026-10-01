import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.CT
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Contract

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage

theorem verifyMessage_verified :
    Verified Arm.target code (Spec.Ed25519.verifyContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => verifyMessage_ok h) verifyMessage_ct
      (.refl verifyMessage_implies.sat_left)) verifyMessage_implies

end VG.Proof.Ed25519.Arm.VerifyMessage
