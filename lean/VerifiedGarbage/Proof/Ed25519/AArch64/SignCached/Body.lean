import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Secret
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

structure NonceReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (L.E + 32) 32 = scalar L m
  nonce : Spec.Ed25519.bytesAt t.mem (L.E + 96) 32 = nonce L m
  point : Spec.Ed25519.bytesAt t.mem (L.out) 32 = Spec.Ed25519.scalarBase (SignCached.nonce L m)

theorem nonce_ok (b : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (hs : SecretReady L m₀ s) :
    WP isa (nonceCode b.code b.suffix) s fun t => Ctx L g vec m₀ t ∧ NonceReady L m₀ t := by
  refine WP.seq (WP.mono (hashNonce_ok b hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.prefixBytes] at du
  have su := (hash_field_bytes hL fu (d := 32) (by decide)).trans hs.scalar
  refine WP.seq (WP.mono (reduce_step hu hL ha 96 (by decide)) fun v ⟨hv, fv, nv⟩ => ?_)
  rw [du] at nv
  have sv := (reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide)).trans su
  refine WP.mono (base_step hv hL ha) fun t ⟨ht, ft, pt⟩ => ⟨ht, ?_, ?_, ?_⟩
  · exact (base_field_bytes hL ft (d := 32) (by decide)).trans sv
  · exact (base_field_bytes hL ft (d := 96) (by decide)).trans nv
  · change Spec.Ed25519.bytesAt v.mem (L.E + 96) 32 = _ at nv
    rw [nv] at pt
    exact pt

theorem challenge_ok (b : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (hs : NonceReady L m₀ s)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (L.seed) 32)) :
    WP isa (challengeCode b.code b.suffix) s fun t => Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (L.seed) 32)
        (Spec.Ed25519.bytesAt m₀ (L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (hashChallenge_ok b hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.point] at du
  have su := (hash_field_bytes hL fu (d := 32) (by decide)).trans hs.scalar
  have nu := (hash_field_bytes hL fu (d := 96) (by decide)).trans hs.nonce
  have pu := (hash_out_bytes hL fu).trans hs.point
  refine WP.seq (WP.mono (reduce_step hu hL ha 128 (by decide)) fun v ⟨hv, fv, cv⟩ => ?_)
  rw [du] at cv
  have sv := (reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide)).trans su
  have nv := (reduce_field_bytes hL fv (d := 96) (by decide) (by decide) (by decide)).trans nu
  have pv := (reduce_out_bytes hL fv (by decide)).trans pu
  refine WP.mono (mul_step hv hL ha) fun t ⟨ht, ft, st⟩ => ⟨ht, ?_⟩
  change Spec.Ed25519.bytesAt v.mem (L.E + 96) 32 = _ at nv
  change Spec.Ed25519.bytesAt v.mem (L.E + 128) 32 = _ at cv
  change Spec.Ed25519.bytesAt v.mem (L.E + 32) 32 = _ at sv
  rw [nv, cv, sv] at st
  have pt := (mul_out_bytes hL ft).trans pv
  rw [Proof.Ed25519.signatureBytes_split, pt]
  change Spec.Ed25519.scalarBase (nonce L m₀) ++ Spec.Ed25519.bytesAt t.mem (L.out + (32 : BitVec 64)) 32 = _
  rw [st]
  exact Proof.Ed25519.sign_pipeline _ _ _ hk

theorem wipe_ok (hc : Ctx L g vec m₀ s) (hL : L.Ok) :
    WP isa (.block wipe) s fun t => Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out) 64 = Spec.Ed25519.bytesAt s.mem (L.out) 64 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 4) (count := 28) (by decide))
    fun t ⟨ht, hf, _⟩ => ⟨ht, ?_⟩
  refine frame_bytes hf L.OUT ?_ (by change 64 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 8 * 4 + 8 * 28 ≤ 256))).symm

theorem body_ok (b : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (L.seed) 32)) :
    WP isa (body b.code b.suffix) s fun t => Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (L.seed) 32)
        (Spec.Ed25519.bytesAt m₀ (L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (secret_ok b hc hL ha) fun u ⟨hu, su⟩ => ?_)
  refine WP.seq (WP.mono (nonce_ok b hu hL ha su) fun v ⟨hv, nv⟩ => ?_)
  refine WP.seq (WP.mono (challenge_ok b hv hL ha nv hk) fun w ⟨hw, sw⟩ => ?_)
  exact WP.mono (wipe_ok hw hL) fun t ⟨ht, same⟩ => ⟨ht, same.trans sw⟩

end VG.Proof.Ed25519.AArch64.SignCached
