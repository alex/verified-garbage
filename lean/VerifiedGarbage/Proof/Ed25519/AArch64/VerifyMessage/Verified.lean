import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.CT
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Contract

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage

theorem verifyMessage_verified (backend : Whole.Backend) :
    Verified AArch64.target (code backend.code backend.suffix) (Spec.Ed25519.verifyContract AArch64.abi 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => verifyMessage_ok backend h) (verifyMessage_ct backend)
      (.refl verifyMessage_implies.sat_left)) verifyMessage_implies

end VG.Proof.Ed25519.AArch64.VerifyMessage
