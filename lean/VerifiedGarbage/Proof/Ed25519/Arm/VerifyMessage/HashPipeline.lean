import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.HashUpdates

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def hashInput (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.bytesAt m (State.addr L.sig) 32 ++
    Spec.Ed25519.bytesAt m (State.addr L.pk) 32 ++
    Spec.Ed25519.bytesAt m (State.addr L.msg) L.len.toNat

theorem sig_prefix_same (hc : Ctx L g m₀ s) (hL : L.Ok) :
    Spec.Ed25519.bytesAt s.mem (State.addr L.sig) 32 = Spec.Ed25519.bytesAt m₀ (State.addr L.sig) 32 := by
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
    WP isa VG.Impl.Ed25519.Arm.VerifyMessage.hash s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E+184) 64 = Spec.Sha512.sha512 (hashInput L m₀) := by
  refine WP.seq (WP.mono (init_step hc hL ha) fun t ⟨ht,_,hinit⟩ => ?_)
  refine WP.seq (WP.mono (update_input ht hL ha 3 0 (by decide) (by decide)
    (signature_input hL) rfl hinit) fun u ⟨hu,_,hsig⟩ => ?_)
  change Spec.Sha512.Repr _ u.mem _ ([] ++ Spec.Ed25519.bytesAt t.mem (State.addr L.sig) 32) at hsig
  rw [List.nil_append,sig_prefix_same ht hL] at hsig
  refine WP.seq (WP.mono (update_input hu hL ha 0 32 (by decide) (by decide)
    (key_input hL) (bytes_length _ _ _).symm hsig) fun w ⟨hw,_,hpk⟩ => ?_)
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt u.mem (State.addr L.pk) 32) at hpk
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32≤2^64; decide)] at hpk
  have hpkl : (Spec.Ed25519.bytesAt m₀ (State.addr L.sig) 32 ++ Spec.Ed25519.bytesAt m₀ (State.addr L.pk) 32).length = 64 := by
    rw [List.length_append,bytes_length,bytes_length]
  refine WP.seq (WP.mono (update_message hw hL ha 64 (by decide) hpkl.symm hpk) fun z ⟨hz,_,hmsg⟩ => ?_)
  have hlen : (hashInput L m₀).length = 64+L.len.toNat := by
    simp only [hashInput,List.length_append,bytes_length]
  refine WP.mono (finalize_step hz hL ha 64 (by decide) true (msg := hashInput L m₀)
    (by rw [hlen]; exact hL.message_bound) (by simp only [ite_true]; rw [hlen]; omega) hmsg)
    fun t ⟨ht,_,hh⟩ => ⟨ht,hh⟩

end VG.Proof.Ed25519.Arm.VerifyMessage
