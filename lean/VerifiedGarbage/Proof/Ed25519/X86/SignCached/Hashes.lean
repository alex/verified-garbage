import VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashSteps

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem hashSeed_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hashSeed s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_input hu hL ha 1 0 (by decide) (seed_input hL)
    (by decide) ru) fun v ⟨hv, fv, rv⟩ => ?_)
  have hs := hu.input_bytes hL (r := L.SEED) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt u.mem (L.seed.setWidth 64) 32 = Spec.Ed25519.bytesAt m₀ (L.seed.setWidth 64) 32 at hs
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (L.seed.setWidth 64) 32) at rv
  rw [List.nil_append, hs] at rv
  refine WP.mono (finalize_step hv hL ha 32 (by decide) false
    (by rw [bytes_length]; decide) (by rw [bytes_length]; rfl) rv)
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans ft), hd⟩

theorem hashNonce_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hashNonce s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 64) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_prefix hu hL ha ru) fun v ⟨hv, fv, rv⟩ => ?_)
  have keep := hash_frame_bytes hL fu (d := 64) (n := 32) (by decide) (by decide)
  change Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + (64 : BitVec 64)) 32 = Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + (64 : BitVec 64)) 32 at keep
  rw [keep] at rv
  refine WP.seq (WP.mono (update_message hv hL ha 32 (by rw [bytes_length]; rfl) rv)
    fun w ⟨hw, fw, rw'⟩ => ?_)
  refine WP.mono (finalize_step hw hL ha 32 (by decide) true ?_ ?_ rw')
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans ft)), hd⟩
  · rw [List.length_append, bytes_length, bytes_length]
    have := L.len.isLt; omega
  · rw [List.length_append, bytes_length, bytes_length]
    simp only [ite_true]; omega

theorem hashChallenge_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hashChallenge s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt s.mem (L.out.setWidth 64) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 ++
          Spec.Ed25519.bytesAt m₀ (L.msg.setWidth 64) L.len.toNat) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun u ⟨hu, fu, ru⟩ => ?_)
  refine WP.seq (WP.mono (update_input hu hL ha 0 0 (by decide) (point_input hL)
    (by decide) ru) fun v ⟨hv, fv, rv⟩ => ?_)
  change Spec.Sha512.Repr _ v.mem _ ([] ++ Spec.Ed25519.bytesAt u.mem (L.out.setWidth 64) 32) at rv
  rw [List.nil_append, hash_out_bytes hL fu] at rv
  refine WP.seq (WP.mono (update_input hv hL ha 2 32 (by decide) (key_input hL)
    (by rw [bytes_length]; rfl) rv) fun w ⟨hw, fw, rw'⟩ => ?_)
  have hk := hv.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  change Spec.Ed25519.bytesAt v.mem (L.pk.setWidth 64) 32 = Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32 at hk
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt v.mem (L.pk.setWidth 64) 32) at rw'
  rw [hk] at rw'
  refine WP.seq (WP.mono (update_message hw hL ha 64 (by rw [List.length_append, bytes_length, bytes_length]; rfl)
    rw') fun z ⟨hz, fz, rz⟩ => ?_)
  refine WP.mono (finalize_step hz hL ha 64 (by decide) true ?_ ?_ rz)
    fun t ⟨ht, ft, hd⟩ => ⟨ht, fu.trans (fv.trans (fw.trans (fz.trans ft))), hd⟩
  · rw [List.length_append, List.length_append, bytes_length, bytes_length, bytes_length]
    have := L.len.isLt; omega
  · rw [List.length_append, List.length_append, bytes_length, bytes_length, bytes_length]
    simp only [ite_true]; omega

end VG.Proof.Ed25519.X86.SignCached
