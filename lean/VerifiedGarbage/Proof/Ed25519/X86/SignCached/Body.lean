import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Secret
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

structure NonceReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem ((fp L 32).setWidth 64) 32 = scalar L m
  nonce : Spec.Ed25519.bytesAt t.mem ((fp L 96).setWidth 64) 32 = nonce L m
  point : Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 32 = Spec.Ed25519.scalarBase (SignCached.nonce L m)

theorem nonce_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (hs : SecretReady L m₀ s) :
    WP isa nonceCode s fun t => Ctx L g m₀ t ∧ NonceReady L m₀ t := by
  refine WP.seq (WP.mono (hashNonce_ok hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.prefixBytes] at du
  have su := (hash_field_bytes hL fu (d := 32) (by decide) (by decide)).trans hs.scalar
  refine WP.seq (WP.mono (reduce_step hu hL ha 96 (by decide) (by decide)) fun v ⟨hv, fv, nv⟩ => ?_)
  rw [du] at nv
  have sv := (reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide) (by decide)).trans su
  refine WP.mono (base_step hv hL ha) fun t ⟨ht, ft, pt⟩ => ⟨ht, ?_, ?_, ?_⟩
  · exact (base_field_bytes hL ft (d := 32) (by decide) (by decide)).trans sv
  · exact (base_field_bytes hL ft (d := 96) (by decide) (by decide)).trans nv
  · rw [nv] at pt
    exact pt

theorem challenge_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (hs : NonceReady L m₀ s)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32)) :
    WP isa challengeCode s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32)
        (Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (hashChallenge_ok hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.point] at du
  have su := (hash_field_bytes hL fu (d := 32) (by decide) (by decide)).trans hs.scalar
  have nu := (hash_field_bytes hL fu (d := 96) (by decide) (by decide)).trans hs.nonce
  have pu := (hash_out_bytes hL fu).trans hs.point
  refine WP.seq (WP.mono (reduce_step hu hL ha 128 (by decide) (by decide)) fun v ⟨hv, fv, cv⟩ => ?_)
  rw [du] at cv
  have sv := (reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide) (by decide)).trans su
  have nv := (reduce_field_bytes hL fv (d := 96) (by decide) (by decide) (by decide) (by decide)).trans nu
  have pv := (reduce_out_bytes hL fv (by decide)).trans pu
  refine WP.mono (mul_step hv hL ha) fun t ⟨ht, ft, st⟩ => ⟨ht, ?_⟩
  rw [nv, cv, sv] at st
  have pt := (mul_out_bytes hL ft).trans pv
  rw [Proof.Ed25519.signatureBytes_split, pt]
  change Spec.Ed25519.scalarBase (nonce L m₀) ++ Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64 + (32 : BitVec 64)) 32 = _
  rw [st]
  exact Proof.Ed25519.sign_pipeline _ _ _ hk

theorem wipe_ok (hc : Ctx L g m₀ s) (hL : L.Ok) :
    WP isa (.block wipe) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 64 = Spec.Ed25519.bytesAt s.mem (L.out.setWidth 64) 64 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 8) (count := 56) (hashSpace hL).frameFit (by decide))
    fun t ⟨ht, hf, _⟩ => ⟨ht, ?_⟩
  refine frame_bytes hf L.OUT ?_ (by change 64 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
    (Offset.sub_base _ (by decide : 4 * 8 + 4 * 56 ≤ 256) p hp))).symm

theorem body_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32)) :
    WP isa body s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32)
        (Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (secret_ok hc hL ha) fun u ⟨hu, su⟩ => ?_)
  refine WP.seq (WP.mono (nonce_ok hu hL ha su) fun v ⟨hv, nv⟩ => ?_)
  refine WP.seq (WP.mono (challenge_ok hv hL ha nv hk) fun w ⟨hw, sw⟩ => ?_)
  exact WP.mono (wipe_ok hw hL) fun t ⟨ht, same⟩ => ⟨ht, same.trans sw⟩

end VG.Proof.Ed25519.X86.SignCached
