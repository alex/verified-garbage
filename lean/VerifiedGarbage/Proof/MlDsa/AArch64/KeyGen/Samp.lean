import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Seeds
import VerifiedGarbage.Proof.MlDsa.KeyGen.Masked

/-!
# ML-DSA key generation on AArch64: the samplers

Untrusted: everything here is checked by Lean. The entries of `Â`
(`expA_piece`) and of `s₁ ‖ s₂` (`expS_piece`): after the first `e` entries
of `Â` and `r` of `s₁ ‖ s₂` (`KSamp`), each polynomial is reduced (and those
of `s₁ ‖ s₂` small), and `x24` is 1 if every sampler succeeded, with the
polynomials those of the standard for some bounds, or 0 if key generation
fails within the least bounds (`Good`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (Params keyGenSeeds Poly IPoly Bounds minBounds rejNTTPoly rejBoundedPoly keyGenInternal toRq
  polyAt coeffAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (seedA seedS Bounds.Le bmax Small ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## What the samplers leave -/

/-- `x24` after the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`: 1 if they
are those of the standard, `A` and `S`, for some bounds; 0 if key generation
fails within the least bounds. -/
def Good (p : Params) (σ : State) (e r : Nat) (A : Nat → Poly) (S : Nat → IPoly) (v : BitVec 64) : Prop :=
  (v = 1 ∧ ∃ b : Bounds, (∀ e' < e, rejNTTPoly b.rejNTT (seedA (rhoOf p σ) (e' / p.ℓ) (e' % p.ℓ)) = some (A e')) ∧
      ∀ r' < r, rejBoundedPoly p.η b.rejBounded (seedS (rho'Of p σ) r') = some (S r')) ∨
    (v = 0 ∧ keyGenInternal p minBounds (xiOf σ) = none)

theorem good_01 {p : Params} {σ : State} {e r : Nat} {A : Nat → Poly} {S : Nat → IPoly} {v : BitVec 64}
    (h : Good p σ e r A S v) : v = 0 ∨ v = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inr h, .inl h]

/-- After the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`. -/
structure KSamp (p : Params) (σ : State) (e r : Nat) (s : State) : Prop where
  k1 : K1 p σ s
  ex : ∃ (A : Nat → Poly) (S : Nat → IPoly), (∀ e' < e, PolyIs s.mem (pa s (aP e')) (A e')) ∧
    (∀ r' < r, PolyIs s.mem (pa s (sP p r')) (toRq (S r')) ∧ Small p.η (S r')) ∧ Good p σ e r A S (s.gpr .x24)

theorem KSamp.keep {p : Params} (hF : PFacts p) {S : Nat} {σ : State} (hp : kgPre p S σ) {e r : Nat} {s s' : State}
    (h : KSamp p σ e r s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : k1Chk p ws = true)
    (ha : ∀ e' < e, keepB kgR (kgW p) ws (aP e') 1024 = true)
    (hs : ∀ r' < r, keepB kgR (kgW p) ws (sP p r') 1024 = true) (h24 : s'.gpr .x24 = s.gpr .x24) :
    KSamp p σ e r s' := by
  have L := h.k1.kc.lay hF hp
  obtain ⟨A, S', hA, hS, hG⟩ := h.ex
  refine ⟨h.k1.step hF hp hP hc, A, S', fun e' he' => L.keepPoly hP (ha e' he') (hA e' he'),
    fun r' hr' => ⟨L.keepPoly hP (hs r' hr') (hS r' hr').1, (hS r' hr').2⟩, by rw [h24]; exact hG⟩

theorem KSamp.zero {p : Params} {σ s : State} (h : K1 p σ s) (h24 : s.gpr .x24 = 1) : KSamp p σ 0 0 s :=
  ⟨h, fun _ => Vector.replicate 256 0, fun _ => Vector.replicate 256 0, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _),
    .inl ⟨h24, ⟨0, 0, 0, 0⟩, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem bytes34 (m : Mem) (a : Addr) : bytesAt m a 34 = bytesAt m a 32 ++ bytesAt m (a + BitVec.ofNat 64 32) 2 :=
  Proof.MlKem.bytesAt_add m a 32 2

theorem sc_add (t : State) (o k : Nat) : pa t (sc o) + BitVec.ofNat 64 k = pa t (sc (o + k)) := by
  rw [pa, pa, BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## An entry of `Â` -/

theorem expA_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {σ : State}
    (hp : kgPre p S σ) {e : Nat} (he : e < p.k * p.ℓ) {s : State} (h : KSamp p σ e 0 s) :
    WP isa (expA P p e) s (KSamp p σ (e + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.k1.kc.lay hF hp
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  unfold expA sampled
  refine WP.seq (WP.mono (setTwo_ok L (o := oSA + 32) (a := e % p.ℓ) (b := e / p.ℓ) (by decide) (by lay) (by lay))
    fun s₁ ⟨hP₁, k₁, hb₁⟩ => ?_)
  have h₁ : KSamp p σ e 0 s₁ :=
    h.keep hF hp hP₁ (by unfold k1Chk kcChk; lay) (fun e' he' => by lay) (fun _ h => absurd h (Nat.not_lt_zero _))
      (k₁.get .x24)
  have L₁ := h₁.k1.kc.lay hF hp
  have hseed : bytesAt s₁.mem (pa s₁ (sc oSA)) 34 = seedA (rhoOf p σ) (e / p.ℓ) (e % p.ℓ) := by
    rw [bytes34, h₁.k1.sa, sc_add, sc_pa hP₁, hb₁, Proof.MlDsa.KeyGen.seedA_eq]
  refine WP.seq (WP.mono (rejNttAt_ok hP.s64 hP.rejNtt L₁ (seed := sc oSA) (a := aP e) (ss := sc oSS)
    (by unfold rejNttChk; lay)) fun s₂ ⟨hP₂, x₂, hred, hout⟩ => ?_)
  rw [hseed] at hout
  have L₂ := L₁.post hP₂
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  refine WP.mono (tail_ok L₂ (a := aP e) (by lay) (by lay) hr01) fun s₃ ⟨hP₃, x₃, hco⟩ => ?_
  have hP₁₃ := PPostB.app hP₂ hP₃ (sc_bases _ (by simp))
  have e₂ : pa s₂ (aP e) = pa s₁ (aP e) := sc_pa hP₂ _
  have e₃ : pa s₃ (aP e) = pa s₂ (aP e) := sc_pa hP₃ _
  rw [e₂] at hco
  obtain ⟨A, S', hA, _, hG⟩ := h₁.ex
  rw [x₂, Proof.MlDsa.KeyGen.and01 (good_01 hG) hr01] at x₃
  refine ⟨h₁.k1.step hF hp hP₁₃ (by unfold k1Chk kcChk; lay), fun e' => if e' = e then polyAt s₃.mem (pa s₃ (aP e))
    else A e', S', fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
  · dsimp only
    rcases (by omega : e' < e ∨ e' = e) with he' | rfl
    · rw [ifn (by omega)]
      exact L₁.keepPoly hP₁₃ (by lay) (hA e' he')
    · rw [ifp rfl]
      refine ⟨?_, rfl⟩
      rw [e₃, e₂]
      by_cases h1 : (s₂.gpr .x0).setWidth 32 = 1
      · exact (Proof.MlDsa.KeyGen.masked_one h1 hco).2 (hred h1)
      · exact (Proof.MlDsa.KeyGen.masked_zero h1 hco).1
  · rw [x₃]
    have hq' : e = p.ℓ * (e / p.ℓ) + e % p.ℓ := (Nat.div_add_mod e p.ℓ).symm
    rcases hG with ⟨h1, b, hb, _⟩ | ⟨h0, hn⟩
    · rcases hout with ⟨ho, b', hb'⟩ | ⟨ho, hn⟩
      · refine .inl ⟨by rw [ifp ⟨h1, ho⟩], bmax b b', fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
        dsimp only
        rcases (by omega : e' < e ∨ e' = e) with he' | rfl
        · rw [ifn (by omega)]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejNTT (hb e' he')
        · rw [ifp rfl, e₃, e₂, (Proof.MlDsa.KeyGen.masked_one ho hco).1]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_right b b').rejNTT hb'
      · rw [ifn (fun h => by rw [h.2] at ho; exact absurd ho (by decide))]
        exact .inr ⟨rfl, Proof.MlDsa.KeyGen.keyGenInternal_none_A hq hr hn⟩
    · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
      exact .inr ⟨rfl, hn⟩

/-! ## Constant time -/

theorem rho_pub {p : Params} {S : Nat} {σ₁ σ₂ : State} (pub : kgPub p S σ₁ σ₂) : rhoOf p σ₁ = rhoOf p σ₂ :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split (kgPub_eq pub).2.1).1

theorem rej_pub {p : Params} {S : Nat} {σ₁ σ₂ : State} (pub : kgPub p S σ₁ σ₂) {r : Nat} (hr : r < p.ℓ + p.k) :
    Spec.MlDsa.rejBoundedLeak p.η (seedS (rho'Of p σ₁) r) = Spec.MlDsa.rejBoundedLeak p.η (seedS (rho'Of p σ₂) r) :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split (kgPub_eq pub).2.1).2 r hr

theorem Two.post {p : Params} {S : Nat} {x y x' y' : State} (T : Two p S x y) {W₁ W₂ : List Region}
    (hx : PostB S x x' W₁) (hy : PostB S y y' W₂) : Two p S x' y' :=
  ⟨T.lx.post hx, T.ly.post hy, fun r hr => by rw [hx.bs r hr, hy.bs r hr]; exact T.same.1 r hr,
    by rw [hx.sp, hy.sp]; exact T.same.2⟩

/-- A piece that leaks the same, and keeps the layout, leaves two runs in it. -/
theorem RelCT.two {p : Params} {S : Nat} {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → Two p S x y)
    (htr : RelCT isa P c fun _ _ => True)
    (hok : ∀ x y, P x y → WP isa c x (fun x' => ∃ W, PostB S x x' W) ∧ WP isa c y (fun y' => ∃ W, PostB S y y' W)) :
    RelCT isa P c (Two p S) :=
  RelCT.postDep htr (F := fun x x' => ∃ W, PostB S x x' W) hok fun x y _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => (hP x y h).post hx hy

/-- The check is the same for every offset: its hint is computed once, for offset 0. -/
theorem mask_taint : ∀ j < 80, (taint.check (AArch64.Taint.ofRegs [.x28]) (mask (sc (oP j)))
    (VG.Taint.hintOf taint (AArch64.Taint.ofRegs [.x28]) (mask (sc 0)))).isSome = true := by decide +kernel

/-- The AND of a sampler's result and the mask of its output. -/
theorem tail_tr {p : Params} {S : Nat} {j : Nat} (hj : j < 80) :
    RelCT isa (Two p S) (.seq (.block and24) (mask (sc (oP j)))) fun _ _ => True :=
  RelCT.seq (Two.step (block_nomem_tr fun i hi _ => by simp only [and24, List.mem_singleton] at hi; subst hi; rfl)
      fun x _ => WP.mono (and24_ok x) fun _ ⟨o, _⟩ =>
        ⟨[], postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _)⟩)
    (taintRel [.x28] (fun _ _ h => Two.x28 h) (mask_taint j hj))

theorem setIJ_taint : ∀ v < 8, ∀ w < 8, (taint.check (AArch64.Taint.ofRegs [.x28])
    (.block (setB (sc (oSA + 32)) v ++ setB (sc (oSA + 33)) w)) (.block [])).isSome = true := by decide +kernel

theorem expA_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {e : Nat}
    (he : e < p.k * p.ℓ) : RelCT isa (R p S (KSamp p · e 0)) (expA P p e) fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  refine rel_of (Q := fun x y => Two p S x y ∧ bytesAt x.mem (pa x (sc oSA)) 32 = bytesAt y.mem (pa y (sc oSA)) 32)
    ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_two hF p₁ p₂ pub h₁.k1.kc h₂.k1.kc, by
      rw [h₁.k1.sa, h₂.k1.sa, rho_pub pub]⟩
  unfold expA sampled
  -- The seed, then the call and the mask.
  let F := fun (x x' : State) => (∃ W, PostB S x x' W) ∧
    bytesAt x'.mem (pa x' (sc oSA)) 34 = bytesAt x.mem (pa x (sc oSA)) 32 ++ [BitVec.ofNat 8 (e % p.ℓ),
      BitVec.ofNat 8 (e / p.ℓ)]
  have hF1 : ∀ x, Lay S kgR (kgW p) x →
      WP isa (.block (setB (sc (oSA + 32)) (e % p.ℓ) ++ setB (sc (oSA + 33)) (e / p.ℓ))) x (F x) := fun x L =>
    WP.mono (setTwo_ok L (o := oSA + 32) (a := e % p.ℓ) (b := e / p.ℓ) (by decide) (by lay) (by lay))
      fun x' ⟨hP₁, _, hb⟩ => ⟨⟨_, hP₁⟩, by rw [bytes34, L.keepBytes hP₁ (by lay), sc_add, sc_pa hP₁, hb]⟩
  refine RelCT.seq (RelCT.postDep (taintRel [.x28] (fun x y h => h.1.x28) (setIJ_taint _ (by omega) _ (by omega)))
    (F := F) (fun x y h => ⟨hF1 x h.1.lx, hF1 y h.1.ly⟩)
    (Q := fun x y => Two p S x y ∧ bytesAt x.mem (pa x (sc oSA)) 34 = bytesAt y.mem (pa y (sc oSA)) 34)
    fun x y x' y' ⟨T, e32⟩ ⟨⟨_, hx⟩, bx⟩ ⟨⟨_, hy⟩, by'⟩ => ⟨T.post hx hy, by rw [bx, by', e32]⟩) ?_
  have hc : rejNttChk kgR (kgW p) (sc oSA) (aP e) (sc oSS) = true := by unfold rejNttChk; lay
  have ok := fun x (L : Lay S kgR (kgW p) x) => WP.mono (rejNttAt_ok hP.s64 hP.rejNtt L hc)
    fun _ h => (⟨_, h.1⟩ : ∃ W, PostB S x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1) (rejNttAt_tr hP.rejNtt (kgOk p) hc fun x y h =>
      ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
      fun x y h => ⟨ok x h.1.lx, ok y h.1.ly⟩)
    (tail_tr (j := e) (by omega))

end VG.Proof.MlDsa.AArch64.KeyGen
