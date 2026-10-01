import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.CTHash

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem update_outArgs (hL : L.Ok) {source count : Nat} {nv : Value} {s : State}
    (hs : OutArgs L [.caller 4 0, .const count, .const 0, .caller source 0, nv, .caller 4 192] s) :
    UpdateArgs L (BitVec.ofNat 32 count) (L.value source) (value L nv) s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hs.slot hL (j := 0) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact hs.slot hL (j := 1) (by simp) (by simp)
  · exact hs.slot hL (j := 2) (by simp) (by simp)
  · exact (hs.slot hL (j := 3) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact hs.slot hL (j := 4) (by simp) (by simp)
  · exact hs.slot hL (j := 5) (by simp) (by simp)

theorem hash_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hash (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have ini := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 4 0] (by decide) (by simp [Whole.valid]) (by taint_decide)
  have rs := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 4 0, .const 0, .const 0, .caller 3 0, .const 32, .caller 4 192]
    (by decide) (by simp [Whole.valid]) (by taint_decide)
  have ps := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 4 0, .const 32, .const 0, .caller 0 0, .const 32, .caller 4 192]
    (by decide) (by simp [Whole.valid]) (by taint_decide)
  have ms := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb [.caller 4 0, .const 64, .const 0, .caller 1 0, .caller 2 0, .caller 4 192]
    (by decide) (by simp [Whole.valid]) (by taint_decide)
  have r := update_call_ct (g₁ := g₁) (g₂ := g₂) (m₁ := m₁) (m₂ := m₂) hL
    (vs := [.caller 4 0, .const 0, .const 0, .caller 3 0, .const 32, .caller 4 192]) rfl
    (input_sig hL) (fun _ hs => update_outArgs hL hs)
  have p := update_call_ct (g₁ := g₁) (g₂ := g₂) (m₁ := m₁) (m₂ := m₂) hL
    (vs := [.caller 4 0, .const 32, .const 0, .caller 0 0, .const 32, .caller 4 192]) rfl
    (input_pk hL) (fun _ hs => update_outArgs hL hs)
  have m := update_call_ct (g₁ := g₁) (g₂ := g₂) (m₁ := m₁) (m₂ := m₂) hL
    (vs := [.caller 4 0, .const 64, .const 0, .caller 1 0, .caller 2 0, .caller 4 192]) rfl
    (input_msg hL) (fun _ hs => by
      have h := update_outArgs hL hs
      simpa only [value, Lay.value, BitVec.add_zero] using h)
  exact (ini.seq (init_call_ct hL)).seq ((rs.seq r).seq ((ps.seq p).seq
    ((ms.seq m).seq ((finalize_args_ct hL ha hb).seq (finalize_call_ct hL _)))))

theorem hash_ct_result (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (he : hashInput L m₁ = hashInput L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) hash
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 =
        Spec.Sha512.sha512 (hashInput L m₁)) := by
  refine two_wp ((hash_ct hL ha hb).mono (fun _ _ h => h) (fun _ _ _ => trivial)) ?_ ?_
  · intro t hc _
    exact hash_ok hc hL ha
  · intro t hc _
    refine WP.mono (hash_ok hc hL hb) fun _ ⟨hu, hd⟩ => ⟨hu, ?_⟩
    rw [he]
    exact hd

end VG.Proof.Ed25519.X86.VerifyMessage
