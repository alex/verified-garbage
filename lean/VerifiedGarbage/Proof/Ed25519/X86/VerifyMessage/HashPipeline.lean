import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.HashInputs
import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.HashFinalize

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def hashInput (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.bytesAt m (L.sig.setWidth 64) 32 ++
    Spec.Ed25519.bytesAt m (L.pk.setWidth 64) 32 ++
    Spec.Ed25519.bytesAt m (L.msg.setWidth 64) L.len.toNat

theorem bytes_length (m : Mem) (p : BitVec 64) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

theorem sig_prefix_same (hc : Ctx L g m₀ s) (hL : L.Ok) :
    Spec.Ed25519.bytesAt s.mem (L.sig.setWidth 64) 32 = Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hc.frame.bytes (R := L.SIG) (by
    intro r hr
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.sc _ (by simp [Lay.inputs])
    · exact (hL.ks _ (by simp [Lay.inputs])).symm)
    (by change 64 ≤ 2 ^ 64; decide) (by change i < 64; have := List.mem_range.mp hi; omega)

theorem hash_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa hash s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = Spec.Sha512.sha512 (hashInput L m₀) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun t ⟨ht, _, hinit⟩ => ?_)
  refine WP.seq (WP.mono (prefix_step ht hL ha (source := 3) (count := 0)
    (by decide) rfl (by decide) (input_sig hL) hinit) fun u ⟨hu, _, hsig⟩ => ?_)
  change Spec.Sha512.Repr _ u.mem _ ([] ++ Spec.Ed25519.bytesAt t.mem (L.sig.setWidth 64) 32) at hsig
  rw [List.nil_append, sig_prefix_same ht hL] at hsig
  refine WP.seq (WP.mono (prefix_step hu hL ha (source := 0) (count := 32)
    (by decide) (bytes_length _ _ _) (by decide) (input_pk hL) hsig) fun v ⟨hv, _, hpk⟩ => ?_)
  change Spec.Sha512.Repr _ v.mem _ (_ ++ Spec.Ed25519.bytesAt u.mem (L.pk.setWidth 64) 32) at hpk
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)] at hpk
  have hpkl : (Spec.Ed25519.bytesAt m₀ (L.sig.setWidth 64) 32 ++
      Spec.Ed25519.bytesAt m₀ (L.pk.setWidth 64) 32).length = 64 := by
    rw [List.length_append, bytes_length, bytes_length]
  refine WP.seq (WP.mono (message_step hv hL ha hpkl hpk) fun w ⟨hw, _, hmsg⟩ => ?_)
  rw [hv.input_bytes hL (r := L.MSG) (by simp [Lay.inputs])
    (by have := L.len.isLt; change L.len.toNat ≤ 2 ^ 64; omega)] at hmsg
  have hlen : (hashInput L m₀).length = L.len.toNat + 64 := by
    simp only [hashInput, List.length_append, bytes_length]
    omega
  refine WP.mono (finalize_step hw hL ha (msg := hashInput L m₀)
    (by rw [hlen]; have := L.len.isLt; omega) hlen.symm hmsg) fun t ⟨ht, _, hd⟩ => ⟨ht, hd⟩

end VG.Proof.Ed25519.X86.VerifyMessage
