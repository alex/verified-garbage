import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Layout
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.HashPre

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (callWith)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem init_step (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith initArgs Spec.Sha512.init512Api.name
      (Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512)) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem L.scr [] := by
  refine WP.seq (WP.mono (setup_ok hc hL ha (args := [(.x0, .caller 2 0)])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])) fun u ⟨hu, _, hs⟩ => ?_)
  have h0 := hs (.x0, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact WP.mono (Whole.init_call hu (Whole.init_pre h0) (Whole.covers_writes hw) hw h0)
    fun v ⟨hv, _, hh⟩ => ⟨hv, hh⟩

theorem update_step (v : Whole.Backend) (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr []) :
    WP isa (callWith updateArgs (Spec.Sha512.updateApi.name ++ v.suffix) v.update) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 u.mem L.scr
        (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.x0, .caller 2 0), (.x1, .const 0), (.x2, .caller 1 0), (.x3, .const 32), (.x4, .caller 2 192)])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have h0 := hs (.x0, .caller 2 0) (by simp)
  have h1 := hs (.x1, .const 0) (by simp)
  have h2 := hs (.x2, .caller 1 0) (by simp)
  have h3 := hs (.x3, .const 32) (by simp)
  have h4 := hs (.x4, .caller 2 192) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3 h4
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  have hp := Whole.update_pre h0 h2 h3 h4 hL.sc (by rw [hu.sp]; exact hL.e16) (by rw [hu.sp]; exact hL.cc)
    (by rw [hu.sp]; exact hL.cs)
  have cv : Covers (Whole.updateRd L.seed 32 ++ Whole.hashWr L.scr)
      (L.inputs ++ Whole.FR L.E :: L.outputs) := by
    intro a n hin
    obtain ⟨r, hr, hh⟩ := hin
    rcases List.mem_append.mp hr with hr | hr
    ·
      simp only [Whole.updateRd, List.mem_singleton] at hr
      subst r
      exact ⟨L.SEED, List.mem_append_left _ (by simp [Lay.inputs]), hh⟩
    · exact Whole.covers_writes hw a n ⟨r, hr, hh⟩
  refine WP.mono (Whole.update_call v hu hp cv hw (prev := []) h0 h2 h3 h1 (hm ▸ hh)) fun u' ⟨hu', _, hr⟩ => ⟨hu', ?_⟩
  simp only [List.nil_append, BitVec.toNat_ofNat] at hr
  rw [hu.seed_bytes hL] at hr
  exact hr

theorem finalize_writes (L : Lay) : ∀ r ∈ Whole.finalizeWr L.scr (L.E + 192),
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0 + 192 ≤ 8192; decide⟩
  · exact .inl ⟨192, rfl, by change 192 + 64 ≤ 256; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192 + 688 ≤ 8192; decide⟩

theorem finalize_step (v : Whole.Backend) (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hh : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr (Spec.Ed25519.bytesAt m₀ L.seed 32)) :
    WP isa (callWith finalizeArgs (Spec.Sha512.finalizeApi.name ++ v.suffix) v.finalize) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Ed25519.bytesAt u.mem (L.E + 192) 64 =
        Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.x0, .caller 2 0), (.x1, .const 32), (.x2, .frame 192), (.x3, .caller 2 192)])
    (by decide) (by simp [Whole.valid]) (by simp) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have h0 := hs (.x0, .caller 2 0) (by simp)
  have h1 := hs (.x1, .const 32) (by simp)
  have h2 := hs (.x2, .frame 192) (by simp)
  have h3 := hs (.x3, .caller 2 192) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2 h3
  have hd : Region.Disjoint ⟨L.E + 192, 64⟩ L.SCR :=
    hL.kc.sub_left (Offset.sub_base _ (by decide : 192 + 64 ≤ 336))
  have hp := Whole.finalize_pre h0 h2 h3 hd (by rw [hu.sp]; exact hL.e16) (by rw [hu.sp]; exact hL.cc)
    (by rw [hu.sp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304))
  have hw := finalize_writes L
  have hl : (Spec.Ed25519.bytesAt m₀ L.seed 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  exact WP.mono (Whole.finalize_call v hu hp (Whole.covers_writes hw) hw h0 h2
    (by rw [hl]; exact h1) (hm ▸ hh) (by rw [hl]; decide)) fun u' ⟨hu', _, hd⟩ => ⟨hu', hd⟩

theorem hash_ok (v : Whole.Backend) (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (hash v.code v.suffix) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (L.E + 192) 64 = Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  exact WP.seq (WP.mono (init_step hc hL ha) fun t₁ ⟨h₁, hh₁⟩ =>
    WP.seq (WP.mono (update_step v h₁ hL ha hh₁) fun t₂ ⟨h₂, hh₂⟩ => finalize_step v h₂ hL ha hh₂))

end VG.Proof.Ed25519.AArch64.PublicKey
