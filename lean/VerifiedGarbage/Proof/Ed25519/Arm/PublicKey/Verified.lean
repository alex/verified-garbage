import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.CT

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

theorem publicKey_verified :
    Verified Arm.target code (Spec.Ed25519.publicKeyContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => publicKey_ok h) publicKey_ct (.refl pk_implies.sat_left))
    pk_implies

end VG.Proof.Ed25519.Arm.PublicKey
