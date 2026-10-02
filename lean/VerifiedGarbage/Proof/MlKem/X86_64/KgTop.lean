import VerifiedGarbage.Proof.MlKem.X86_64.KgCT

/-!
# ML-KEM on x86-64: key generation

The function, piece by piece (`KeyGen.*_ok`): it returns 1 with
`KeyGen_internal(d, z)` in `ek` and `dk` if every `SampleNTT` succeeded within
280 iterations (`allOk`), and 0 otherwise (`keyGen_correct`); it leaks only
the pointers and `ρ` (`keyGen_ct`). Each parameter set's file moves this to
its shared contract.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

/-- `KB` is kept by a piece that only sets flags. -/
theorem KB.flag {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {e : Nat} (he : e ≤ L.k * L.k)
    {s s' : State} (h : KB L e σ s) (hP : PPost s s' []) : KB L e σ s' := by
  have L₀ := h.a.kc.lay W hp
  exact ⟨h.a.keep W hp hP.b W.flag W.flagG W.flagS W.flagB, by rw [hP.cs .r15 (by decide)]; exact h.m.r15,
    fun e' he' f hf => L₀.keepPoly hP.b (W.flagA e' (by omega)) (h.m.mat e' he' f hf)⟩

/-- At the end: `r15` as `allOk`, and the keys if it is 1. -/
structure KEnd (L : Kem) (σ s : State) : Prop where
  kc : KC σ s
  r15 : s.gpr .r15 = if allOk L.k (rhoK L σ) (L.k * L.k) then 1 else 0
  keys : allOk L.k (rhoK L σ) (L.k * L.k) → KFin L σ s

theorem r15_ne {k : Nat} {ρ : List Byte} {r : BitVec 64} (h : r = if allOk k ρ (k * k) then 1 else 0)
    (hne : r.setWidth 32 ≠ 0) : allOk k ρ (k * k) := by
  by_contra ho
  rw [ifn ho] at h
  exact hne (by rw [h]; rfl)

theorem r15_eq {k : Nat} {ρ : List Byte} {r : BitVec 64} (h : r = if allOk k ρ (k * k) then 1 else 0)
    (he : r.setWidth 32 = 0) : ¬ allOk k ρ (k * k) := by
  intro ho
  rw [ifp ho] at h
  rw [h] at he
  exact absurd he (by decide)

theorem rest_ok (v : Sample4Impl) {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {s : State}
    (h : KRest0 L σ s) : WP isa (rest L v.callee) s (KFin L σ) := by
  unfold rest
  refine WP.seq (WP.mono (prfs_okK v W hp h) fun s₀ h₀ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => KRest L k 0 0 σ) (2 * L.k) 0
    (fun k _ hk s hs => se_ok v.arith W hp (by omega) hs) s₀ h₀) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => KRest L (2 * L.k) k 0 σ) L.k 0
    (fun k _ hk s hs => row_ok v.arith W hp (by omega) hs) s₁ (by rwa [Nat.zero_add] at h₁)) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => KRest L (2 * L.k) L.k k σ) L.k 0
    (fun k _ hk s hs => encS_ok W hp (by omega) hs) s₂ (by rwa [Nat.zero_add] at h₂)) fun s₃ h₃ => ?_)
  exact fin_ok W hp (by rwa [Nat.zero_add] at h₃)

theorem body_ok (v : Sample4Impl) {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {s : State}
    (h : KB L (L.k * L.k) σ s) : WP isa (ifOk (rest L v.callee)) s (KEnd L σ) := by
  refine ifOk_ok (fun s₁ hP hne => ?_) fun s₁ hP he => ?_
  · have ho := r15_ne h.m.r15 hne
    exact WP.mono (rest_ok v W hp (KRest0.start (h.flag W hp (Nat.le_refl _) hP) ho)) fun s' hf =>
      ⟨hf.kc, by rw [hf.r15, ifp ho], fun _ => hf⟩
  · have ho := r15_eq h.m.r15 he
    have h' := h.flag W hp (Nat.le_refl _) hP
    exact ⟨h'.a.kc, h'.m.r15, fun h => absurd h ho⟩

/-- The postcondition, from the keys. -/
theorem post_of {L : Kem} (W : KgWf L) {σ s : State} (h : KEnd L σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) : (keyGenK L).post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rsi := by
    rw [pa, h.kc.top.regs (.r12, .rsi) (by decide), add_ofNat_zero]
  have e13 : pa s (.r13, 0) = σ.gpr .rdx := by
    rw [pa, h.kc.top.regs (.r13, .rdx) (by decide), add_ofNat_zero]
  show Outcome _ _ _
  by_cases ho : allOk L.k (rhoK L σ) (L.k * L.k)
  · have hf := h.keys ho
    refine .inl ⟨by rw [hr, hf.r15]; rfl, minIterations, ?_⟩
    show keyGenInternal L.p minIterations _ _ = _
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_some W.eta.1 (a := aHat (rhoK L σ))
      fun i hi j hj => aHat_eq ho hi hj, Option.map_some, hm, ← e12, ← e13, hf.ek, hf.dk]
  · refine .inr ⟨by rw [hr, h.r15, ifn ho]; rfl, ?_⟩
    obtain ⟨i, hi, j, hj, hn⟩ := not_allOk ho
    show keyGenInternal L.p minIterations _ _ = _
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_none hi hj hn]
    rfl

theorem KEnd.hin {L : Kem} (W : KgWf L) {σ s : State} (hp : (keyGenK L).pre σ) (h : KEnd L σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk =>
  (h.kc.lay W hp).cR (W.sv k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

end KeyGen

open KeyGen in
theorem kemKeyGen_correct (v : Sample4Impl) {L : Kem} (W : KgWf L) (hctl : ctlOk (kemKeyGen L v.callee) = true)
    (σ : State) (hp : (keyGenK L).pre σ) :
    ∃ t s', Exec isa (kemKeyGen L v.callee) σ t s' ∧ abiPreserved σ s' ∧ (keyGenK L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (gRho_ok W hp h₁ h15) fun s₂ ⟨h₂, h15'⟩ =>
      WP.seq (WP.mono (samples_ok v W hp (KB.zero h₂ h15')) fun s₃ h₃ =>
        WP.seq (WP.mono (body_ok v W hp h₃) fun s₄ h₄ =>
          WP.mono (topEpi_ok h₄.kc.top (h₄.hin W hp)) fun s₅ ⟨hr, hg, hm⟩ =>
            (⟨hg, post_of W h₄ hr hm⟩ : gprPreserved σ s₅ ∧ (keyGenK L).post σ s₅)))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

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

variable {L : Kem} (W : KgWf L)
include W

abbrev R (L : Kem) (I : State → State → Prop) : State → State → Prop := Rel2 (keyGenK L).pre (keyGenK L).pub I

theorem rest_tr (v : Sample4Impl) :
    RelCT isa (R L fun σ s => KRest0 L σ s ∧ allOk L.k (rhoK L σ) (L.k * L.k)) (rest L v.callee)
      (R L fun σ s => KFin L σ s ∧ allOk L.k (rhoK L σ) (L.k * L.k)) := by
  unfold rest
  refine RelCT.seq (relInvC (fun σ s hp hs => prfs_okK v W hp hs) (prfs_trK W v)) ?_
  refine RelCT.seq (seqR_tr (R := fun k => R L fun σ s => KRest L k 0 0 σ s ∧ allOk L.k (rhoK L σ) (L.k * L.k))
    (2 * L.k) 0 fun k _ hk => relInvC (fun σ s hp hs => se_ok v.arith W hp (by omega) hs)
      (se_tr W v.arith (by omega))) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (seqR_tr (R := fun k => R L fun σ s => KRest L (2 * L.k) k 0 σ s ∧ allOk L.k (rhoK L σ) (L.k * L.k))
    L.k 0 fun k _ hk => relInvC (fun σ s hp hs => row_ok v.arith W hp (by omega) hs) (row_tr W v.arith (by omega))) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (seqR_tr (R := fun k => R L fun σ s => KRest L (2 * L.k) L.k k σ s ∧ allOk L.k (rhoK L σ) (L.k * L.k))
    L.k 0 fun k _ hk => relInvC (fun σ s hp hs => encS_ok W hp (by omega) hs) (encS_tr W (by omega))) ?_
  rw [Nat.zero_add]
  exact relInvC (fun σ s hp hs => fin_ok W hp hs) (fin_tr W)

omit W in
theorem r15_pub {σ₁ σ₂ x y : State} (pub : (keyGenK L).pub σ₁ σ₂) (h₁ : KB L (L.k * L.k) σ₁ x)
    (h₂ : KB L (L.k * L.k) σ₂ y) : x.gpr .r15 = y.gpr .r15 := by
  rw [h₁.m.r15, h₂.m.r15]; exact congrArg (fun ρ => if allOk L.k ρ (L.k * L.k) then (1 : BitVec 64) else 0) (rho_pub pub)

theorem body_tr (v : Sample4Impl) : RelCT isa (R L (KB L (L.k * L.k))) (ifOk (rest L v.callee)) (R L (KEnd L)) := by
  refine ifOk_tr (fun x y ⟨_, _, _, _, pub, h₁, h₂⟩ => by rw [r15_pub pub h₁ h₂]) ?_ ?_
  · refine RelCT.mono (rest_tr W v) (fun x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, hne⟩ => ?_)
      fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
        ⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁.1.kc, by rw [h₁.1.r15, ifp h₁.2], fun _ => h₁.1⟩,
          ⟨h₂.1.kc, by rw [h₂.1.r15, ifp h₂.2], fun _ => h₂.1⟩⟩
    have o₁ := r15_ne h₁.m.r15 hne
    have o₂ : allOk L.k (rhoK L σ₂) (L.k * L.k) := by rw [← rho_pub pub]; exact o₁
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨KRest0.start (h₁.flag W p₁ (Nat.le_refl _) hx) o₁, o₁⟩,
      ⟨KRest0.start (h₂.flag W p₂ (Nat.le_refl _) hy) o₂, o₂⟩⟩
  · rintro x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, he⟩
    have o₁ := r15_eq h₁.m.r15 he
    have o₂ : ¬ allOk L.k (rhoK L σ₂) (L.k * L.k) := by rw [← rho_pub pub]; exact o₁
    have k₁ := h₁.flag W p₁ (Nat.le_refl _) hx
    have k₂ := h₂.flag W p₂ (Nat.le_refl _) hy
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨k₁.a.kc, k₁.m.r15, fun h => absurd h o₁⟩, ⟨k₂.a.kc, k₂.m.r15, fun h => absurd h o₂⟩⟩

omit W in
theorem pro_tr : RelCT isa (R L fun σ s => s = σ) (.block pro) fun _ _ => True :=
  taintRel [.rcx, .rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa4 pub.2.2.2.1 pub.1 pub.2.1 pub.2.2.1) (by taint_decide)

omit W in
theorem epi_tr : RelCT isa (R L (KEnd L)) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.kc.top.regs (.rbx, .rcx) (by decide), h₂.kc.top.regs (.rbx, .rcx) (by decide), pub.2.2.2.1])
    (by taint_decide)

end KeyGen

open KeyGen in
theorem kemKeyGen_ct (v : Sample4Impl) {L : Kem} (W : KgWf L) :
    ConstantTime isa (keyGenK L).pre (keyGenK L).pub (kemKeyGen L v.callee) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemKeyGen
  refine RelCT.seq (relInv (I' := fun σ s => KC σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok W hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := fun σ s => KA L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => gRho_ok W hp hs.1 hs.2) (gRho_tr W)) ?_
  refine RelCT.seq (RelCT.mono (samples_tr W v)
    (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, KB.zero h₁.1 h₁.2, KB.zero h₂.1 h₂.2⟩)
    fun _ _ h => h) ?_
  exact RelCT.seq (body_tr W v) (RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.MlKem.X86_64
