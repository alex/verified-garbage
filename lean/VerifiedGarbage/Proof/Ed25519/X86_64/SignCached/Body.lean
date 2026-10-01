import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Finish
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Complete RFC 8032 signing, including all three SHA-512 computations. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem body_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hlen : 64 + L.len.toNat < 2 ^ 64)
    (hpk : Spec.Ed25519.bytesAt m₀ L.pk 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ L.seed 32)) :
    WP isa (body v.callee v.suffix) t fun t' => Ctx L g mx m₀ t' ∧ Spec.Ed25519.bytesAt t'.mem L.out 64 =
      Spec.Ed25519.sign (Spec.Ed25519.bytesAt m₀ L.seed 32) (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) := by
  apply WP.assoc
  refine WP.seq (WP.mono (secret_ok v hL hc) fun u ⟨hu, hs⟩ => ?_)
  apply WP.assoc
  apply WP.assoc
  refine WP.seq (WP.mono (WP.assoc' (nonce_ok v hL hu hs hlen)) fun w ⟨hw, hn⟩ => ?_)
  apply WP.assoc
  exact WP.seq (WP.mono (challenge_ok v hL hw hn hlen) fun z ⟨hz, hk⟩ => finish_ok hL hz hk hpk)

end VG.Proof.Ed25519.X86_64.SignCached
