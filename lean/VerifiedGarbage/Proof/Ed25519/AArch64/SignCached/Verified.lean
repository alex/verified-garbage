import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.CT
import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Contract

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

theorem signCached_verified (v : Whole.Backend) :
    Verified AArch64.target (code v.code v.suffix) (Spec.Ed25519.signCachedContract AArch64.abi 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => signCached_ok v h) (signCached_ct v) (.refl signCached_implies.sat_left))
    signCached_implies

end VG.Proof.Ed25519.AArch64.SignCached
