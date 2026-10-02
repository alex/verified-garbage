import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.CTHash

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem hash_ct (backend : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hash backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have i := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb initValues
    (by decide) (by simp [initValues,Whole.valid]) (by simp [initValues,known])
    (by simp [initValues,preserved]) (by taint_decide)
  have r := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb (prefixValues 3 0)
    (by decide) (by simp [prefixValues,Whole.valid]) (by simp [prefixValues,known])
    (by simp [prefixValues,preserved]) (by taint_decide)
  have a := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb (prefixValues 0 32)
    (by decide) (by simp [prefixValues,Whole.valid]) (by simp [prefixValues,known])
    (by simp [prefixValues,preserved]) (by taint_decide)
  have m := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb messageValues
    (by decide) (by simp [messageValues,Whole.valid]) (by simp [messageValues,known])
    (by simp [messageValues,preserved]) (by taint_decide)
  have f := setup_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) hL ha hb finalizeValues
    (by decide) (by simp [finalizeValues,Whole.valid]) (by simp [finalizeValues,known])
    (by simp [finalizeValues,preserved]) (by taint_decide)
  have rc := update_call_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (m₁ := m₁) (m₂ := m₂)
    backend (args := prefixValues 3 0) (prefix_ready hL (input_sig hL).1 (input_sig hL).2)
    (by simp [prefixValues])
  have ac := update_call_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (m₁ := m₁) (m₂ := m₂)
    backend (args := prefixValues 0 32) (prefix_ready hL (input_pk hL).1 (input_pk hL).2)
    (by simp [prefixValues])
  have mc := update_call_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (m₁ := m₁) (m₂ := m₂)
    backend (args := messageValues) (message_ready hL) (by simp [messageValues])
  exact (i.seq init_call_ct).seq ((r.seq rc).seq ((a.seq ac).seq ((m.seq mc).seq (f.seq (finalize_call_ct backend hL)))))

/-- Public inputs give a common digest for the equation check that follows. -/
theorem hash_result_ct (backend : Whole.Backend) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hm : hashInput L m₁ = hashInput L m₂) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (hash backend.code backend.suffix)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E+192) 64 =
        Spec.Sha512.sha512 (hashInput L m₁)) := by
  refine two_wp ((hash_ct backend hL ha hb).mono (fun _ _ h => h) (fun _ _ _ => trivial)) ?_ ?_
  · intro s hc _
    exact hash_ok backend hc hL ha
  · intro s hc _
    have h := hash_ok backend hc hL hb
    rw [← hm] at h
    exact h

end VG.Proof.Ed25519.AArch64.VerifyMessage
