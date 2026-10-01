import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.CT

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

theorem publicKey_verified (v : Whole.Backend) :
    Verified AArch64.target (code v.code v.suffix) (Spec.Ed25519.publicKeyContract AArch64.abi 336) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => publicKey_ok v h) (publicKey_ct v) (.refl pk_implies.sat_left))
    pk_implies

end VG.Proof.Ed25519.AArch64.PublicKey
