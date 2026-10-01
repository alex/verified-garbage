import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Challenge

/-! Complete the signature and clear the secret frame values. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (callWith scalarMulAdd)
open VG.Impl.Ed25519.X86_64.SignCached
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def finishCode : Prog isa := .seq (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) (.block wipe)

theorem finish_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (hs : ChallengeReady L m₀ t)
    (hpk : Spec.Ed25519.bytesAt m₀ L.pk 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ L.seed 32)) :
    WP isa finishCode t fun t' => Ctx L g mx m₀ t' ∧ Spec.Ed25519.bytesAt t'.mem L.out 64 =
      Spec.Ed25519.sign (Spec.Ed25519.bytesAt m₀ L.seed 32) (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) := by
  refine WP.seq (WP.mono (mul_step hL hc) fun u ⟨hu, ho, hf⟩ => ?_)
  rw [hs.nonce, hs.challenge, hs.scalar] at ho
  have hp := (mul_out_bytes hL hf).trans hs.point
  have hout : Spec.Ed25519.bytesAt u.mem L.out 64 =
      Spec.Ed25519.sign (Spec.Ed25519.bytesAt m₀ L.seed 32) (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) := by
    rw [Proof.Ed25519.signatureBytes_split, hp, ho]
    exact Proof.Ed25519.sign_pipeline _ _ _ hpk
  refine WP.mono (wipe_ok hu) fun w ⟨hw, hfw⟩ => ⟨hw, ?_⟩
  have he := frame_bytes hfw L.OUT (by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hL.ko.sub_left (Offset.sub_base L.B (d := 16) (n := 192) (by decide))).symm)
    (by decide : 64 ≤ 2 ^ 64)
  exact he.trans hout

end VG.Proof.Ed25519.X86_64.SignCached
