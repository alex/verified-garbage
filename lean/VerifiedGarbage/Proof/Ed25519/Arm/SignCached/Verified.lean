import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Correct
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.CT
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Contract

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

theorem signCached_verified :
    Verified Arm.target code (Spec.Ed25519.signCachedContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => signCached_ok h) signCached_ct (.refl signCached_implies.sat_left))
    signCached_implies

end VG.Proof.Ed25519.Arm.SignCached
