import VerifiedGarbage.Proof.MlKem.X86_64.KgCT

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_keygen`

Untrusted: everything here is checked by Lean. The function, piece by
piece (`KeyGen.*_ok`): it returns 1 with `KeyGen_internal(d, z)` in `ek`
and `dk` if every `SampleNTT` succeeded within 280 iterations (`allOk`),
and 0 otherwise (`keyGen_correct`); it leaks only the pointers and `ρ`
(`keyGen_ct`); so it meets the shared contract (`keyGen_verified`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

/-- `KB` is kept by a piece that only sets flags. -/
theorem KB.flag {σ : State} (hp : keyGenK.pre σ) {e : Nat} (he : e ≤ 9) {s s' : State} (h : KB e σ s)
    (hP : PPost s s' []) : KB e σ s' := by
  have L := h.a.kc.lay hp
  refine ⟨⟨h.a.kc.step hp hP.b (by decide), by rw [L.keepBytes hP.b (by decide)]; exact h.a.rho,
    by rw [L.keepBytes hP.b (by decide)]; exact h.a.sig, by rw [L.keepBytes hP.b (by decide)]; exact h.a.sb⟩,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun e' he' f hf => ?_⟩
  have hk : ∀ e < 9, keepB kgB [] (aS (e / 3) (e % 3)) 1024 = true := by decide
  exact L.keepPoly hP.b (hk e' (by omega)) (h.mat e' he' f hf)

/-- At the end: `r15` as `allOk`, and the keys if it is 1. -/
structure KEnd (σ s : State) : Prop where
  kc : KC σ s
  r15 : s.gpr .r15 = if allOk (rhoK σ) 9 then 1 else 0
  keys : allOk (rhoK σ) 9 → KFin σ s

theorem r15_ne {ρ : List Byte} {r : BitVec 64} (h : r = if allOk ρ 9 then 1 else 0) (hne : r.setWidth 32 ≠ 0) :
    allOk ρ 9 := by
  by_contra ho
  rw [ifn ho] at h
  exact hne (by rw [h]; rfl)

theorem r15_eq {ρ : List Byte} {r : BitVec 64} (h : r = if allOk ρ 9 then 1 else 0) (he : r.setWidth 32 = 0) :
    ¬ allOk ρ 9 := by
  intro ho
  rw [ifp ho] at h
  rw [h] at he
  exact absurd he (by decide)

theorem rest_ok {σ : State} (hp : keyGenK.pre σ) {s : State} (h : KRest 0 0 0 σ s) :
    WP isa rest s (KFin σ) := by
  unfold rest
  refine WP.seq (WP.mono (seqR_ok (I := fun k => KRest k 0 0 σ) 6 0 (fun k _ hk s hs => se_ok hp (by omega) hs) s h)
    fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => KRest 6 k 0 σ) 3 0 (fun k _ hk s hs => row_ok hp (by omega) hs) s₁ h₁)
    fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => KRest 6 3 k σ) 3 0 (fun k _ hk s hs => encS_ok hp (by omega) hs) s₂
    h₂) fun s₃ h₃ => ?_)
  exact fin_ok hp h₃

theorem body_ok {σ : State} (hp : keyGenK.pre σ) {s : State} (h : KB 9 σ s) : WP isa (ifOk rest) s (KEnd σ) := by
  refine ifOk_ok (fun s₁ hP hne => ?_) fun s₁ hP he => ?_
  · have ho := r15_ne h.r15 hne
    exact WP.mono (rest_ok hp (KRest.start (h.flag hp (by decide) hP) ho)) fun s' hf =>
      ⟨hf.kc, by rw [hf.r15, ifp ho], fun _ => hf⟩
  · have ho := r15_eq h.r15 he
    have h' := h.flag hp (by decide) hP
    exact ⟨h'.a.kc, h'.r15, fun h => absurd h ho⟩

/-- The postcondition, from the keys. -/
theorem post_of {σ s : State} (h : KEnd σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) : keyGenK.post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rsi := by
    rw [pa, h.kc.top.regs (.r12, .rsi) (by decide), add_ofNat_zero]
  have e13 : pa s (.r13, 0) = σ.gpr .rdx := by
    rw [pa, h.kc.top.regs (.r13, .rdx) (by decide), add_ofNat_zero]
  show Outcome _ _ _
  by_cases ho : allOk (rhoK σ) 9
  · have hf := h.keys ho
    refine .inl ⟨by rw [hr, hf.r15]; rfl, minIterations, ?_⟩
    show keyGenInternal mlKem768 minIterations _ _ = _
    rw [keyGenInternal768, kpkeKeyGen768_some (a := aHat (rhoK σ)) fun i hi j hj => aHat_eq ho hi hj, Option.map_some,
      hm, ← e12, ← e13, hf.ek, hf.dk]
  · refine .inr ⟨by rw [hr, h.r15, ifn ho]; rfl, ?_⟩
    obtain ⟨i, hi, j, hj, hn⟩ := not_allOk ho
    show keyGenInternal mlKem768 minIterations _ _ = _
    rw [keyGenInternal768, kpkeKeyGen768_none hi hj hn]
    rfl

end KeyGen

theorem KeyGen.KEnd.hin {σ s : State} (hp : keyGenK.pre σ) (h : KeyGen.KEnd σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk => by
  have hk' : ∀ k < 6, inB KeyGen.kgB (sc (oSV + 8 * k)) 8 = true := by decide
  exact (h.kc.lay hp).cR (hk' k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

open KeyGen in
theorem keyGen_correct (σ : State) (hp : keyGenK.pre σ) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.keyGen σ t s' ∧ abiPreserved σ s' ∧ keyGenK.post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (gRho_ok hp h₁ h15) fun s₂ ⟨h₂, h15'⟩ =>
      WP.seq (WP.mono (samples_ok hp (KB.zero h₂ h15')) fun s₃ h₃ =>
        WP.seq (WP.mono (body_ok hp h₃) fun s₄ h₄ =>
          WP.mono (topEpi_ok h₄.kc.top (h₄.hin hp)) fun s₅ ⟨hr, hg, hm⟩ =>
            (⟨hg, post_of h₄ hr hm⟩ : gprPreserved σ s₅ ∧ keyGenK.post σ s₅)))))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.1, hF.2⟩

/-! ## Constant time -/

/-- `relInv`, with a fact about the entry state carried along. -/
theorem relInvC {Pre : State → Prop} {Pub : State → State → Prop} {I I' : State → State → Prop} {C : State → Prop}
    {c : Prog isa} (hw : ∀ σ s, Pre σ → I σ s → WP isa c s (I' σ))
    (ht : RelCT isa (Rel2 Pre Pub I) c fun _ _ => True) :
    RelCT isa (Rel2 Pre Pub fun σ s => I σ s ∧ C σ) c (Rel2 Pre Pub fun σ s => I' σ s ∧ C σ) :=
  relInv (fun σ s hp hs => WP.mono (hw σ s hp hs.1) fun _ h => ⟨h, hs.2⟩)
    (RelCT.mono ht (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, i₁.1, i₂.1⟩) fun _ _ h => h)

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

abbrev R (I : State → State → Prop) : State → State → Prop := Rel2 keyGenK.pre keyGenK.pub I

theorem rest_tr : RelCT isa (R fun σ s => KRest 0 0 0 σ s ∧ allOk (rhoK σ) 9) rest
    (R fun σ s => KFin σ s ∧ allOk (rhoK σ) 9) := by
  unfold rest
  refine RelCT.seq (seqR_tr (R := fun k => R fun σ s => KRest k 0 0 σ s ∧ allOk (rhoK σ) 9) 6 0
    fun k _ hk => relInvC (fun σ s hp hs => se_ok hp (by omega) hs) (se_tr (by omega))) ?_
  refine RelCT.seq (seqR_tr (R := fun k => R fun σ s => KRest 6 k 0 σ s ∧ allOk (rhoK σ) 9) 3 0
    fun k _ hk => relInvC (fun σ s hp hs => row_ok hp (by omega) hs) (row_tr (by omega))) ?_
  refine RelCT.seq (seqR_tr (R := fun k => R fun σ s => KRest 6 3 k σ s ∧ allOk (rhoK σ) 9) 3 0
    fun k _ hk => relInvC (fun σ s hp hs => encS_ok hp (by omega) hs) (encS_tr (by omega))) ?_
  exact relInvC (fun σ s hp hs => fin_ok hp hs) fin_tr

theorem r15_pub {σ₁ σ₂ x y : State} (pub : keyGenK.pub σ₁ σ₂) (h₁ : KB 9 σ₁ x) (h₂ : KB 9 σ₂ y) :
    x.gpr .r15 = y.gpr .r15 := by
  have e : kgRho (kgD σ₁) = kgRho (kgD σ₂) := rho_pub pub
  rw [h₁.r15, h₂.r15, e]

theorem body_tr : RelCT isa (R (KB 9)) (ifOk rest) (R KEnd) := by
  refine ifOk_tr (fun x y ⟨_, _, _, _, pub, h₁, h₂⟩ => by rw [r15_pub pub h₁ h₂]) ?_ ?_
  · refine RelCT.mono rest_tr (fun x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, hne⟩ => ?_)
      fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
        ⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁.1.kc, by rw [h₁.1.r15, ifp h₁.2], fun _ => h₁.1⟩,
          ⟨h₂.1.kc, by rw [h₂.1.r15, ifp h₂.2], fun _ => h₂.1⟩⟩
    have o₁ := r15_ne h₁.r15 hne
    have o₂ : allOk (rhoK σ₂) 9 := by
      have e : kgRho (kgD σ₁) = kgRho (kgD σ₂) := rho_pub pub
      show allOk (kgRho (kgD σ₂)) 9
      rw [← e]; exact o₁
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨KRest.start (h₁.flag p₁ (by decide) hx) o₁, o₁⟩,
      ⟨KRest.start (h₂.flag p₂ (by decide) hy) o₂, o₂⟩⟩
  · rintro x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, he⟩
    have o₁ := r15_eq h₁.r15 he
    have o₂ : ¬ allOk (rhoK σ₂) 9 := by
      have e : kgRho (kgD σ₁) = kgRho (kgD σ₂) := rho_pub pub
      show ¬ allOk (kgRho (kgD σ₂)) 9
      rw [← e]; exact o₁
    have k₁ := h₁.flag p₁ (by decide) hx
    have k₂ := h₂.flag p₂ (by decide) hy
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨k₁.a.kc, k₁.r15, fun h => absurd h o₁⟩, ⟨k₂.a.kc, k₂.r15, fun h => absurd h o₂⟩⟩

theorem pro_tr : RelCT isa (R fun σ s => s = σ) (.block pro) fun _ _ => True :=
  taintRel [.rcx, .rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa4 pub.2.2.2.1 pub.1 pub.2.1 pub.2.2.1) (by taint_decide)

theorem epi_tr : RelCT isa (R KEnd) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.kc.top.regs (.rbx, .rcx) (by decide), h₂.kc.top.regs (.rbx, .rcx) (by decide), pub.2.2.2.1])
    (by taint_decide)

end KeyGen

open KeyGen in
theorem keyGen_ct : ConstantTime isa keyGenK.pre keyGenK.pub Impl.MlKem.X86_64.keyGen := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold Impl.MlKem.X86_64.keyGen
  refine RelCT.seq (relInv (I' := fun σ s => KC σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KA σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => gRho_ok hp hs.1 hs.2) gRho_tr) ?_
  refine RelCT.seq (RelCT.mono (seqR_tr (R := fun e => R (KB e)) 9 0
    fun e _ he => relInv (fun σ s hp hs => sample_step hp (by omega) hs) (sample_tr (by omega)))
    (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, KB.zero h₁.1 h₁.2, KB.zero h₂.1 h₂.2⟩)
    fun _ _ h => h) ?_
  exact RelCT.seq body_tr (RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial)

/-- A state satisfying `keyGenContract`'s precondition. -/
def keyGenSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1184⟩, ⟨0x3000, 2400⟩, ⟨0x10000, 32768⟩]

theorem keyGen_verified :
    Verified X86_64.target Impl.MlKem.X86_64.keyGen (Spec.MlKem.keyGenContract X86_64.abi 24) :=
  Verified.of_correct keyGen_correct keyGen_ct
    { pre := by sig_implies_pre [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenK, X86_64.abi,
        VG.X86_64.argRegs]
      post := by sig_implies_post [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenK, X86_64.abi,
        VG.X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, keyGenK, X86_64.abi,
        VG.X86_64.argRegs] [keyGenSat] using keyGenSat }

end VG.Proof.MlKem.X86_64
