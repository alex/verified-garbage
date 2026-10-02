import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Seeds
import VerifiedGarbage.Proof.MlDsa.KeyGen.Masked

/-!
# ML-DSA key generation on AArch64: the samplers

The entries of `Â` (`expA_piece`) and of `s₁ ‖ s₂` (`expS_piece`): after the
first `e` entries of `Â` and `r` of `s₁ ‖ s₂` (`KSamp`), each polynomial is
reduced (and those of `s₁ ‖ s₂` small), and `x24` is 1 if every sampler
succeeded, with the polynomials those of the standard for some bounds, or 0 if
key generation fails within the least bounds (`Good`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
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
  ⟨T.lx.post hx, T.ly.post hy, fun r hr => by rw [hx.bs r (bases_kept r hr), hy.bs r (bases_kept r hr)]; exact T.same.1 r hr,
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
  have ok := fun x (L : Lay S kgR (kgW p) x) => WP.mono (rejNttAt_ok (nm := "vg_mldsa_rej_ntt_poly" ++ P.suffix) hP.s64 hP.rejNtt L hc)
    fun _ h => (⟨_, h.1⟩ : ∃ W, PostB S x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1) (rejNttAt_tr hP.rejNtt (kgOk p) hc fun x y h =>
      ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
      fun x y h => ⟨ok x h.1.lx, ok y h.1.ly⟩)
    (tail_tr (j := e) (by omega))

/-! ## An entry of `s₁ ‖ s₂` -/

theorem eta_of {p : Params} (hF : PFacts p) : p.η = 2 ∨ p.η = 4 := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inl h, .inr h]

theorem bytes66 (m : Mem) (a : Addr) :
    bytesAt m a 66 = bytesAt m a 64 ++ bytesAt m (a + BitVec.ofNat 64 64) 1 ++ bytesAt m (a + BitVec.ofNat 64 65) 1 := by
  rw [show (66 : Nat) = 64 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add]

/-- The seed of `RejBoundedPoly`, once its index is set. -/
theorem sbSeed {p : Params} {S : Nat} {s s' : State} (L : Lay S kgR (kgW p) s) {r : Nat} (hr : r < 256)
    (hP : PPostB S s s' [(sc (oSB + 64), 1)]) (hb : s'.mem = s.mem.writeW (pa s (sc (oSB + 64))) (BitVec.ofNat 8 r))
    {ρ' : List Byte} (h64 : bytesAt s.mem (pa s (sc oSB)) 64 = ρ') (h65 : bytesAt s.mem (pa s (sc (oSB + 65))) 1 = [0]) :
    bytesAt s'.mem (pa s' (sc oSB)) 66 = Proof.MlDsa.KeyGen.seedS ρ' r := by
  have hsc := scr_eq p
  have k64 := L.keepBytes hP (p := sc oSB) (l := 64) (by lay)
  have k65 := L.keepBytes hP (p := sc (oSB + 65)) (l := 1) (by lay)
  rw [sc_pa hP] at k64 k65 ⊢
  rw [bytes66, k64, h64, sc_add, sc_add, k65, h65, hb, bytesAt_one, writeW8_self, Proof.MlDsa.KeyGen.seedS_eq _ hr,
    List.append_assoc]
  rfl

theorem expS_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {σ : State}
    (hp : kgPre p S σ) {r : Nat} (hr : r < p.ℓ + p.k) {s : State} (h : KSamp p σ (p.k * p.ℓ) r s) :
    WP isa (expS P p r) s (KSamp p σ (p.k * p.ℓ) (r + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.k1.kc.lay hF hp
  unfold expS sampled
  refine WP.seq (WP.mono (setB_ok L (p := sc (oSB + 64)) (v := r) (by decide) (by lay)
    (show Reg.x28 ∈ keptRegs by decide)) fun s₁ ⟨hP₁, k₁, hb₁⟩ => ?_)
  have h₁ : KSamp p σ (p.k * p.ℓ) r s₁ :=
    h.keep hF hp hP₁ (by unfold k1Chk kcChk; lay) (fun e' he' => by lay) (fun r' hr' => by lay) (k₁.get .x24)
  have L₁ := h₁.k1.kc.lay hF hp
  have hseed := sbSeed L (by omega) hP₁ hb₁ h.k1.sb h.k1.z
  refine WP.seq (WP.mono (rejBAt_ok hP.s64 hP.rejBounded L₁ (seed := sc oSB) (a := sP p r) (ss := sc oSS)
    (by unfold rejBChk; lay) (eta_of hF)) fun s₂ ⟨hP₂, x₂, hred, hout⟩ => ?_)
  rw [hseed] at hout
  have L₂ := L₁.post hP₂
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  refine WP.mono (tail_ok L₂ (a := sP p r) (by lay) (by lay) hr01) fun s₃ ⟨hP₃, x₃, hco⟩ => ?_
  have hP₁₃ := PPostB.app hP₂ hP₃ (sc_bases _ (by simp))
  have e₂ : pa s₂ (sP p r) = pa s₁ (sP p r) := sc_pa hP₂ _
  have e₃ : pa s₃ (sP p r) = pa s₂ (sP p r) := sc_pa hP₃ _
  rw [e₂] at hco
  obtain ⟨A, S', hA, hS, hG⟩ := h₁.ex
  rw [x₂, Proof.MlDsa.KeyGen.and01 (good_01 hG) hr01] at x₃
  have k1 := h₁.k1.step hF hp hP₁₃ (by unfold k1Chk kcChk; lay)
  have kA : ∀ e' < p.k * p.ℓ, PolyIs s₃.mem (pa s₃ (aP e')) (A e') := fun e' he' =>
    L₁.keepPoly hP₁₃ (by lay) (hA e' he')
  have kS : ∀ r' < r, PolyIs s₃.mem (pa s₃ (sP p r')) (toRq (S' r')) ∧ Small p.η (S' r') := fun r' hr' =>
    ⟨L₁.keepPoly hP₁₃ (by lay) (hS r' hr').1, (hS r' hr').2⟩
  by_cases ho : (s₂.gpr .x0).setWidth 32 = 1
  · -- The sampler succeeded.
    obtain ⟨b', hb'⟩ : ∃ b' : Bounds, (rejBoundedPoly p.η b'.rejBounded (seedS (rho'Of p σ) r)).map toRq =
        some (polyAt s₂.mem (pa s₁ (sP p r))) := by
      rcases hout with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · rw [h] at ho; exact absurd ho (by decide)
    obtain ⟨x, hx, htx⟩ := Option.map_eq_some_iff.mp hb'
    refine ⟨k1, A, fun r' => if r' = r then x else S' r', kA, fun r' hr' => ?_, ?_⟩
    · dsimp only
      rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
      · rw [ifn (by omega)]; exact kS r' hr'
      · rw [ifp rfl, e₃, e₂, htx, ← (Proof.MlDsa.KeyGen.masked_one ho hco).1]
        exact ⟨⟨(Proof.MlDsa.KeyGen.masked_one ho hco).2 (hred ho), rfl⟩,
          Proof.MlDsa.KeyGen.rejBoundedPoly_range hx⟩
    · rw [x₃]
      rcases hG with ⟨h1, b, hbA, hbS⟩ | ⟨h0, hn⟩
      · refine .inl ⟨by rw [ifp ⟨h1, ho⟩], bmax b b', fun e' he' =>
          Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejNTT (hbA e' he'),
          fun r' hr' => ?_⟩
        dsimp only
        rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
        · rw [ifn (by omega)]
          exact Proof.MlDsa.KeyGen.rejBoundedPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejBounded
            (hbS r' hr')
        · rw [ifp rfl]
          exact Proof.MlDsa.KeyGen.rejBoundedPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_right b b').rejBounded hx
      · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
        exact .inr ⟨rfl, hn⟩
  · -- It failed: the polynomial is zero.
    have hn : rejBoundedPoly p.η minBounds.rejBounded (seedS (rho'Of p σ) r) = none := by
      rcases hout with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h ho
      · exact Option.map_eq_none_iff.mp h
    refine ⟨k1, A, fun r' => if r' = r then Vector.replicate 256 0 else S' r', kA, fun r' hr' => ?_, ?_⟩
    · dsimp only
      rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
      · rw [ifn (by omega)]; exact kS r' hr'
      · rw [ifp rfl, e₃, e₂]
        exact ⟨Proof.MlDsa.KeyGen.masked_zero ho hco, Proof.MlDsa.KeyGen.small_zero _⟩
    · rw [x₃, ifn (fun h => ho h.2)]
      exact .inr ⟨rfl, Proof.MlDsa.KeyGen.keyGenInternal_none_S hr hn⟩

theorem setS_taint : ∀ v < 16, (taint.check (AArch64.Taint.ofRegs [.x28]) (.block (setB (sc (oSB + 64)) v))
    (.block [])).isSome = true := by decide +kernel

theorem expS_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {r : Nat}
    (hr : r < p.ℓ + p.k) : RelCT isa (R p S (KSamp p · (p.k * p.ℓ) r)) (expS P p r) fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  refine rel_of (Q := fun x y => Two p S x y ∧ ∃ ρ₁ ρ₂ : List Byte, bytesAt x.mem (pa x (sc oSB)) 64 = ρ₁ ∧
      bytesAt x.mem (pa x (sc (oSB + 65))) 1 = [0] ∧ bytesAt y.mem (pa y (sc oSB)) 64 = ρ₂ ∧
      bytesAt y.mem (pa y (sc (oSB + 65))) 1 = [0] ∧
      Spec.MlDsa.rejBoundedLeak p.η (seedS ρ₁ r) = Spec.MlDsa.rejBoundedLeak p.η (seedS ρ₂ r))
    ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_two hF p₁ p₂ pub h₁.k1.kc h₂.k1.kc, _, _, h₁.k1.sb, h₁.k1.z, h₂.k1.sb,
      h₂.k1.z, rej_pub pub hr⟩
  unfold expS sampled
  let F := fun (x x' : State) => (∃ W, PostB S x x' W) ∧ ∀ ρ' : List Byte, bytesAt x.mem (pa x (sc oSB)) 64 = ρ' →
    bytesAt x.mem (pa x (sc (oSB + 65))) 1 = [0] → bytesAt x'.mem (pa x' (sc oSB)) 66 = seedS ρ' r
  have hF1 : ∀ x, Lay S kgR (kgW p) x → WP isa (.block (setB (sc (oSB + 64)) r)) x (F x) := fun x L =>
    WP.mono (setB_ok L (p := sc (oSB + 64)) (v := r) (by decide) (by lay) (show Reg.x28 ∈ keptRegs by decide))
      fun x' ⟨hP₁, _, hb⟩ => ⟨⟨_, hP₁⟩, fun _ h64 h65 => sbSeed L (by omega) hP₁ hb h64 h65⟩
  refine RelCT.seq (RelCT.postDep (taintRel [.x28] (fun x y h => h.1.x28) (setS_taint _ (by omega)))
    (F := F) (fun x y h => ⟨hF1 x h.1.lx, hF1 y h.1.ly⟩)
    (Q := fun x y => Two p S x y ∧ Spec.MlDsa.rejBoundedLeak p.η (bytesAt x.mem (pa x (sc oSB)) 66) =
      Spec.MlDsa.rejBoundedLeak p.η (bytesAt y.mem (pa y (sc oSB)) 66))
    fun x y x' y' ⟨T, _, _, a1, a2, a3, a4, a5⟩ ⟨⟨_, hx⟩, bx⟩ ⟨⟨_, hy⟩, by'⟩ =>
      ⟨T.post hx hy, by rw [bx _ a1 a2, by' _ a3 a4, a5]⟩) ?_
  have hc : rejBChk kgR (kgW p) (sc oSB) (sP p r) (sc oSS) = true := by unfold rejBChk; lay
  have ok := fun x (L : Lay S kgR (kgW p) x) => WP.mono (rejBAt_ok hP.s64 hP.rejBounded L hc (eta_of hF))
    fun _ h => (⟨_, h.1⟩ : ∃ W, PostB S x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1) (rejBAt_tr hP.rejBounded (kgOk p) hc (eta_of hF) fun x y h =>
      ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
      fun x y h => ⟨ok x h.1.lx, ok y h.1.ly⟩)
    (tail_tr (j := p.k * p.ℓ + r) (by omega))

/-! ## The pieces -/

theorem expA_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {e : Nat}
    (he : e < p.k * p.ℓ) : Piece p S (KSamp p · e 0) (KSamp p · (e + 1) 0) (expA P p e) :=
  ⟨fun _ _ hp h => expA_ok hP hF hp he h, expA_tr hP hF he⟩

theorem expS_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {r : Nat}
    (hr : r < p.ℓ + p.k) :
    Piece p S (KSamp p · (p.k * p.ℓ) r) (KSamp p · (p.k * p.ℓ) (r + 1)) (expS P p r) :=
  ⟨fun _ _ hp h => expS_ok hP hF hp hr h, expS_tr hP hF hr⟩

/-- The entries of `Â`. -/
theorem sampA_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) :
    Piece p S (fun σ s => K1 p σ s ∧ s.gpr .x24 = 1) (fun σ s => KSamp p σ (p.k * p.ℓ) 0 s)
      (seqR (expA P p) 0 (p.k * p.ℓ)) := by
  refine Piece.mono (Piece.seqR (I := fun e σ s => KSamp p σ e 0 s) (p.k * p.ℓ) 0
    fun e _ he => expA_piece hP hF (by omega)) (fun σ s _ h => KSamp.zero h.1 h.2) fun σ s _ h => ?_
  simpa using h

/-- The entries of `s₁ ‖ s₂`. -/
theorem sampS_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) :
    Piece p S (fun σ s => KSamp p σ (p.k * p.ℓ) 0 s) (fun σ s => KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s)
      (seqR (expS P p) 0 (p.ℓ + p.k)) := by
  refine Piece.mono (Piece.seqR (I := fun r σ s => KSamp p σ (p.k * p.ℓ) r s) (p.ℓ + p.k) 0
    fun r _ hr => expS_piece hP hF (by omega)) (fun _ _ _ h => h) fun σ s _ h => ?_
  simpa using h

end VG.Proof.MlDsa.AArch64.KeyGen
