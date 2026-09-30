import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTCompute

/-!
# ML-DSA verification on x86-64: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

Untrusted: everything here is checked by Lean. For primitives `P` that meet
their contracts (`PrimsOk`), `verify P p` meets `verifyContract p`
(`verify_verified`): it is correct (`verify_correct`) and leaks only its
inputs, which the contract makes public (`verify_ct`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt)

theorem body_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    RelCT isa (RV p fun σ s => T p σ s ∧ s.gpr .r15 = flag True) (body P p) (RV p (T p)) := by
  unfold body
  refine RelCT.seq (hint_tr C hp) (ifOk_rel hp (fun _ _ h => h.1) ?_ ?_ (RelCT.seq (zs_tr C hp)
    (ifOk_rel hp (fun _ _ h => Iz.t h) ?_ ?_ (RelCT.seq (samples_tr C hp)
      (RelCT.mono (compute_tr C hp) ?_ fun _ _ h => h)))))
  · rintro x y ⟨σ₁, σ₂, _, _, pub, i₁, i₂⟩
    rw [S1.r15 i₁, S1.r15 i₂, pub.2.2.2.2.2.2.2]
  · intro σ s₀ s hv h₀ hP e hne
    have t₀ := h₀.1
    unfold S1 at h₀
    obtain ⟨_, hm⟩ := h₀
    split at hm
    · rename_i h hh
      obtain ⟨h15, hH⟩ := hm
      obtain ⟨_, _, kh, _⟩ := parChk p hp
      exact ⟨h, hh, t₀.step hp hv hP (tChk_nil p hp), (t₀.lay hp hv).keepHint hP kh hH,
        fun _ h => absurd h (Nat.not_lt_zero _), by rw [e, h15]; exact flag_congr (by simp)⟩
    · exact absurd (by rw [hm]; rfl) hne
  · rintro x y ⟨σ₁, σ₂, _, _, pub, ⟨_, _, hx⟩, ⟨_, _, hy⟩⟩
    rw [hx.r15, hy.r15, pub.2.2.2.2.2.2.2]
  · rintro σ s₀ s hv ⟨h, hh, hs⟩ hP e hne
    have hn := flag_ne (by rw [← hs.r15]; exact hne)
    exact ⟨h, ⟨hh, hn⟩, hs.flag hp hv (Nat.le_refl _) hP e, by rw [e, hs.r15]; exact flag_congr (iff_true_intro hn)⟩
  · rintro x y ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, _, hx⟩, ⟨h₂, _, hy⟩⟩
    obtain ⟨q₁, e₁, _, _⟩ := hx.ok
    obtain ⟨q₂, e₂, _, _⟩ := hy.ok
    exact ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, _, q₁, _, hx.toSC e₁⟩, ⟨h₂, _, q₂, _, hy.toSC e₂⟩⟩

theorem verify_ct {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    ConstantTime isa (verifyK p).pre (verifyK p).pub (verify P p) := by
  unfold verify
  exact relStart (RelCT.seq (relInv (I' := fun σ s => T p σ s ∧ s.gpr .r15 = flag True)
    (fun σ s hv hs => by subst hs; exact pro_ok hp hv) pro_tr) (RelCT.seq (body_tr C hp) epi_tr))

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]

/-- A state satisfying `verifyContract`'s precondition. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rdx => 0x30000 | .rcx => 0x40000 | .rsp => 0x200000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x10000, p.pkLen⟩, ⟨0x20000, 64⟩, ⟨0x30000, p.sigLen⟩]
  wr := [⟨0x40000, scrLen p⟩]

theorem verify_sat : ∀ p ∈ params, ∃ s, (verifyContract p X86_64.abi 24).pre s := by
  intro p hp
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] [verifySat] using verifySat mlDsa44
  · sig_implies_sat [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] [verifySat] using verifySat mlDsa65
  · sig_implies_sat [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] [verifySat] using verifySat mlDsa87

theorem verify_implies {p : Params} (hp : p ∈ params) : (verifyK p).Implies (verifyContract p X86_64.abi 24) where
  pre s h := by
    sig_pre [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := h
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩
  post s s' _ h := by
    sig_post [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
    have e := map_toNat_inj hb
    obtain ⟨e₁, e₃⟩ := List.append_inj' e (by simp only [Proof.MlKem.bytesAt_length])
    obtain ⟨e₁, e₂⟩ := List.append_inj' e₁ (by simp only [Proof.MlKem.bytesAt_length])
    exact ⟨hdi, hsi, hdx, hcx, hsp, e₁, e₂, e₃⟩
  sat := verify_sat p hp

/-- `verify P p` meets `verifyContract p` with 24 bytes of stack. -/
theorem verify_verified {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    Verified X86_64.target (verify P p) (verifyContract p X86_64.abi 24) :=
  Verified.of_correct (verify_correct C hp) (verify_ct C hp) (verify_implies hp)

end VG.Proof.MlDsa.X86_64.Verify
