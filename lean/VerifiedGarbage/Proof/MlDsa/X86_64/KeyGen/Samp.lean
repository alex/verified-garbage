import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Seeds

/-!
# ML-DSA key generation on x86-64: the samplers

Untrusted: everything here is checked by Lean. The entries of `Â`
(`expA_piece`) and of `s₁ ‖ s₂` (`expS_piece`): after the first `e` entries
of `Â` and `r` of `s₁ ‖ s₂` (`KSamp`), each polynomial is reduced (and those
of `s₁ ‖ s₂` small), and `r15` is 1 if every sampler succeeded, with the
polynomials those of the standard for some bounds, or 0 if key generation
fails within the least bounds (`Good`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc setB)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds integerToBytes Poly IPoly Bounds minBounds rejNTTPoly rejBoundedPoly
  keyGenInternal toRq polyAt coeffAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (seedA seedS Bounds.Le bmax)
open VG.Spec.Sha3 (bytesAt)

/-! ## Polynomials kept by a piece -/

section
variable {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay rbs wbs s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
  {q : Ptr} (hc : keepB (rbs ++ wbs) ws q 1024 = true)
include L hP hc

theorem polyAt_frame' : polyAt s'.mem (pa s' q) = polyAt s.mem (pa s q) := by
  rw [hP.pa (keepB_cs hc)]
  have := L.keepBytes hP hc
  rw [hP.pa (keepB_cs hc)] at this
  exact Proof.MlDsa.KeyGen.polyAt_congr (Proof.MlDsa.KeyGen.bytes_of_bytesAt this)

theorem polyIs_frame' {f : Poly} (h : PolyIs s.mem (pa s q) f) : PolyIs s'.mem (pa s' q) f := by
  rw [hP.pa (keepB_cs hc)]
  have := L.keepBytes hP hc
  rw [hP.pa (keepB_cs hc)] at this
  exact Proof.MlDsa.KeyGen.polyIs_congr (Proof.MlDsa.KeyGen.bytes_of_bytesAt this) h

theorem reduced_frame' (h : Reduced s.mem (pa s q)) : Reduced s'.mem (pa s' q) := by
  rw [hP.pa (keepB_cs hc)]
  have := L.keepBytes hP hc
  rw [hP.pa (keepB_cs hc)] at this
  exact Proof.MlDsa.KeyGen.reduced_congr (Proof.MlDsa.KeyGen.bytes_of_bytesAt this) h

end

/-! ## What the samplers leave -/

/-- The coefficients of `x` are in `[-η, η]`. -/
def Small (η : Nat) (x : IPoly) : Prop := ∀ c ∈ x.toList, -(η : Int) ≤ c ∧ c ≤ η

/-- `r15` after the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`: 1 if they
are those of the standard, `A` and `S`, for some bounds; 0 if key generation
fails within the least bounds. -/
def Good (p : Params) (σ : State) (e r : Nat) (A : Nat → Poly) (S : Nat → IPoly) (v : BitVec 64) : Prop :=
  (v = 1 ∧ ∃ b : Bounds, (∀ e' < e, rejNTTPoly b.rejNTT (seedA (rhoOf p σ) (e' / p.ℓ) (e' % p.ℓ)) = some (A e')) ∧
      ∀ r' < r, rejBoundedPoly p.η b.rejBounded (seedS (rho'Of p σ) r') = some (S r')) ∨
    (v = 0 ∧ keyGenInternal p minBounds (xiOf σ) = none)

/-- After the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`. -/
structure KSamp (p : Params) (σ : State) (e r : Nat) (s : State) : Prop where
  k1 : K1 p σ s
  ex : ∃ (A : Nat → Poly) (S : Nat → IPoly), (∀ e' < e, PolyIs s.mem (pa s (aP e')) (A e')) ∧
    (∀ r' < r, PolyIs s.mem (pa s (sP p r')) (toRq (S r')) ∧ Small p.η (S r')) ∧ Good p σ e r A S (s.gpr .r15)

theorem KSamp.keep {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ) {e r : Nat} {s s' : State}
    (h : KSamp p σ e r s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hx : MX s' = MX s)
    (hc : k1Chk p ws = true) (ha : ∀ e' < e, keepB (kgB p) ws (aP e') 1024 = true)
    (hs : ∀ r' < r, keepB (kgB p) ws (sP p r') 1024 = true) (h15 : s'.gpr .r15 = s.gpr .r15) :
    KSamp p σ e r s' := by
  have L := h.k1.kc.lay hF hp
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  refine ⟨h.k1.step hF hp hP hx hc, A, S, fun e' he' => ?_, fun r' hr' => ?_, by rw [h15]; exact hG⟩
  · exact polyIs_frame' L hP (ha e' he') (hA e' he')
  · exact ⟨polyIs_frame' L hP (hs r' hr') (hS r' hr').1, (hS r' hr').2⟩

/-! ## A masked polynomial -/

theorem polyAt_coeff {m m' : Mem} {q : Addr} (h : ∀ i < 256, coeffAt m' q i = coeffAt m q i) :
    polyAt m' q = polyAt m q :=
  Vector.ext fun i hi => by simp only [polyAt, Vector.getElem_ofFn, h i hi]

/-- Kept if the sampler succeeded. -/
theorem masked_one {m m' : Mem} {q : Addr} {r : BitVec 32} (hr : r = 1)
    (h : ∀ i < 256, coeffAt m' q i = if r = 1 then coeffAt m q i else 0) :
    polyAt m' q = polyAt m q ∧ (Reduced m q → Reduced m' q) := by
  have h' : ∀ i < 256, coeffAt m' q i = coeffAt m q i := fun i hi => by rw [h i hi, ifp hr]
  exact ⟨polyAt_coeff h', fun hq i hi => by rw [h' i hi]; exact hq i hi⟩

/-- Zero if it failed. -/
theorem masked_zero {m m' : Mem} {q : Addr} {r : BitVec 32} (hr : r ≠ 1)
    (h : ∀ i < 256, coeffAt m' q i = if r = 1 then coeffAt m q i else 0) :
    PolyIs m' q (toRq (Vector.replicate 256 0)) := by
  have h' : ∀ i < 256, coeffAt m' q i = 0 := fun i hi => by rw [h i hi, ifn hr]
  refine ⟨fun i hi => by rw [h' i hi]; decide, Vector.ext fun i hi => ?_⟩
  simp only [polyAt, Vector.getElem_ofFn, h' i hi, toRq, Vector.getElem_map, Vector.getElem_replicate]
  rfl

theorem small_zero (η : Nat) : Small η (Vector.replicate 256 0) := fun c hc => by
  rw [Vector.mem_toList_iff, Vector.mem_replicate] at hc
  rw [hc.2]; omega

theorem outcome_01 {α : Type} {f : Bounds → Option α} {r : BitVec 32} {out : α}
    (h : Spec.MlDsa.Outcome f r out) : r = 0 ∨ r = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inr h, .inl h]

theorem r15_and {v : BitVec 64} (hv : v = 0 ∨ v = 1) {r : BitVec 32} (hr : r = 0 ∨ r = 1) :
    BitVec.setWidth 64 (v.setWidth 32 &&& r) = if v = 1 ∧ r = 1 then 1 else 0 := by
  rcases hv with rfl | rfl <;> rcases hr with rfl | rfl <;> decide

theorem good_01 {p : Params} {σ : State} {e r : Nat} {A : Nat → Poly} {S : Nat → IPoly} {v : BitVec 64}
    (h : Good p σ e r A S v) : v = 0 ∨ v = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inr h, .inl h]

theorem sc1_bases (o n : Nat) : ∀ w ∈ [(sc o, n)], w.1.1 ∈ bases := fun w hw => by
  rw [List.mem_singleton] at hw; subst hw; exact rbx_bases

/-! ## An entry of `Â` -/

theorem seedA_eq (ρ : List Byte) (r s : Nat) :
    seedA ρ r s = ρ ++ [BitVec.ofNat 8 s, BitVec.ofNat 8 r] := by
  simp only [seedA, Proof.MlDsa.KeyGen.integerToBytes_one, List.append_assoc]; rfl

theorem expA_ok {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ)
    {e : Nat} (he : e < p.k * p.ℓ) {s : State} (h : KSamp p σ e 0 s) : WP isa (expA P p e) s (KSamp p σ (e + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have L := h.k1.kc.lay hF hp
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  unfold expA
  refine WP.seq (WP.mono (setTwo_ok L (o := oSA + 32) (a := e % p.ℓ) (b := e / p.ℓ) (by omega) (by omega)
    (by lay) (by lay) (by lay)) fun s₁ ⟨hP₁, hx₁, hb₁⟩ => ?_)
  have h₁ : KSamp p σ e 0 s₁ := by
    refine h.keep hF hp hP₁.b hx₁ ?_ (fun e' he' => ?_) (fun _ h => absurd h (Nat.not_lt_zero _))
      (hP₁.cs .r15 (by decide))
    · layk
    · layk
  have S₁ := h₁.k1.kc.site hF hp
  have hseed : bytesAt s₁.mem (pa s₁ (sc oSA)) 34 = seedA (rhoOf p σ) (e / p.ℓ) (e % p.ℓ) := by
    rw [show 34 = 32 + 2 from rfl, Proof.MlKem.bytesAt_add, h₁.k1.sa,
      show pa s₁ (sc oSA) + BitVec.ofNat 64 32 = pa s₁ (sc (oSA + 32)) from off_add _ _ _, hP₁.pa rbx_cs, hb₁,
      seedA_eq]
  refine WP.seq (WP.mono (rejNttAt_ok (sd := sc oSA) (a := aP e) (sc_ok _ (by decide)) (sc_ok _ (by simp only [oP]; omega))
    (by lay) (by lay) (by lay) (by lay) (by lay) hP.rejNtt S₁) fun s₂ ⟨hP₂, hx₂, hred, hout⟩ => ?_)
  rw [hseed] at hout
  have hP₂' : PPostB s₁ s₂ [(aP e, 1024), (sc VG.Impl.MlKem.X86_64.oSS, 2048)] := hP₂.b
  have L₂ := S₁.lay.post hP₂'  (kgB_bases p)
  have hr01 := outcome_01 hout
  refine WP.mono (mask_ok L₂ (a := aP e) (sc_ok _ (by simp only [oP]; omega)) (show Reg.rbx ≠ .r15 by decide) (by lay) hr01)
    fun s₃ ⟨hP₃, hx₃, h15, hco⟩ => ?_
  have hP₃' : PPostB s₂ s₃ [(aP e, 1024)] := hP₃
  have hP₁₃ := PPostB.app hP₂' hP₃' (sc1_bases _ _)
  have L₁ := S₁.lay
  have e₂ : pa s₂ (aP e) = pa s₁ (aP e) := hP₂'.pa rbx_bases
  have e₃ : pa s₃ (aP e) = pa s₂ (aP e) := hP₃'.pa rbx_bases
  rw [e₂] at hco
  obtain ⟨A, S, hA, _, hG⟩ := h₁.ex
  have h15₂ : s₂.gpr .r15 = s₁.gpr .r15 := hP₂.cs .r15 (by decide)
  rw [h15₂, r15_and (good_01 hG) hr01] at h15
  refine ⟨h₁.k1.step hF hp hP₁₃ (hx₃.trans hx₂) (by layk), fun e' => if e' = e then polyAt s₃.mem (pa s₃ (aP e))
    else A e', S, fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
  · dsimp only
    rcases (by omega : e' < e ∨ e' = e) with he' | rfl
    · rw [ifn (by omega)]
      exact polyIs_frame' L₁ hP₁₃ (by layk) (hA e' he')
    · rw [ifp rfl]
      refine ⟨?_, rfl⟩
      rw [e₃, e₂]
      by_cases h1 : (s₂.gpr .rax).setWidth 32 = 1
      · exact (masked_one h1 hco).2 (hred h1)
      · exact (masked_zero h1 hco).1
  · rw [h15]
    have hq' : e = p.ℓ * (e / p.ℓ) + e % p.ℓ := (Nat.div_add_mod e p.ℓ).symm
    rcases hG with ⟨h1, b, hb, _⟩ | ⟨h0, hn⟩
    · rcases hout with ⟨ho, b', hb'⟩ | ⟨ho, hn⟩
      · refine .inl ⟨by rw [ifp ⟨h1, ho⟩], bmax b b', fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
        dsimp only
        rcases (by omega : e' < e ∨ e' = e) with he' | rfl
        · rw [ifn (by omega)]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejNTT (hb e' he')
        · rw [ifp rfl, e₃, e₂, (masked_one ho hco).1]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_right b b').rejNTT hb'
      · rw [ifn (fun h => by rw [h.2] at ho; exact absurd ho (by decide))]
        exact .inr ⟨rfl, Proof.MlDsa.KeyGen.keyGenInternal_none_A hq hr hn⟩
    · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
      exact .inr ⟨rfl, hn⟩

/-! ## Constant time -/

theorem rho_pub {p : Params} {σ₁ σ₂ : State} (pub : (kgK p).pub σ₁ σ₂) : rhoOf p σ₁ = rhoOf p σ₂ :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split pub.2.2.2.2.2).1

theorem rej_pub {p : Params} {σ₁ σ₂ : State} (pub : (kgK p).pub σ₁ σ₂) {r : Nat} (hr : r < p.ℓ + p.k) :
    Spec.MlDsa.rejBoundedLeak p.η (seedS (rho'Of p σ₁) r) = Spec.MlDsa.rejBoundedLeak p.η (seedS (rho'Of p σ₂) r) :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split pub.2.2.2.2.2).2 r hr

theorem Two.post {p : Params} {x y x' y' : State} (T : Two p x y) {W₁ W₂ : List Region} (hx : PostB x x' W₁)
    (hy : PostB y y' W₂) : Two p x' y' :=
  ⟨⟨T.sx.lay.post hx (kgB_bases p), by rw [hx.rsp]; exact T.sx.h24⟩,
    ⟨T.sy.lay.post hy (kgB_bases p), by rw [hy.rsp]; exact T.sy.h24⟩,
    fun r hr => by
      have hb : r ∈ bases := by simp only [kgRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
                                rcases hr with rfl | rfl | rfl | rfl <;> decide
      rw [hx.bs r hb, hy.bs r hb]; exact T.regs r hr, by rw [hx.rsp, hy.rsp]; exact T.rsp⟩

/-- A piece that leaks the same, and keeps the layout, leaves two runs in it. -/
theorem RelCT.two {p : Params} {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → Two p x y)
    (htr : RelCT isa P c fun _ _ => True)
    (hok : ∀ x y, P x y → WP isa c x (fun x' => ∃ W, PostB x x' W) ∧ WP isa c y (fun y' => ∃ W, PostB y y' W)) :
    RelCT isa P c (Two p) :=
  RelCT.postDep htr (F := fun x x' => ∃ W, PostB x x' W) hok fun x y _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => (hP x y h).post hx hy

theorem setIJ_taint : ∀ v < 8, ∀ w < 8, (taint.check (X86_64.Taint.ofRegs [.rbx])
    (.block (setB (sc (oSA + 32)) v ++ setB (sc (oSA + 33)) w)) (.block [])).isSome = true := by decide +kernel

theorem expA_tr {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p) {e : Nat} (he : e < p.k * p.ℓ) :
    RelCT isa (R p (KSamp p · e 0)) (expA P p e) fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  refine rel_of (Q := fun x y => Two p x y ∧ bytesAt x.mem (pa x (sc oSA)) 32 = bytesAt y.mem (pa y (sc oSA)) 32)
    ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_two hF p₁ p₂ pub h₁.k1.kc h₂.k1.kc, by rw [h₁.k1.sa, h₂.k1.sa, rho_pub pub]⟩
  unfold expA
  -- The seed, then the call and the mask.
  let F := fun (x x' : State) => (∃ W, PostB x x' W) ∧
    bytesAt x'.mem (pa x' (sc oSA)) 34 = bytesAt x.mem (pa x (sc oSA)) 32 ++ [BitVec.ofNat 8 (e % p.ℓ),
      BitVec.ofNat 8 (e / p.ℓ)]
  have hF1 : ∀ x, Site p x → WP isa (.block (setB (sc (oSA + 32)) (e % p.ℓ) ++ setB (sc (oSA + 33)) (e / p.ℓ))) x
      (F x) := fun x S =>
    WP.mono (setTwo_ok S.lay (o := oSA + 32) (a := e % p.ℓ) (b := e / p.ℓ) (by omega) (by omega) (by lay) (by lay)
      (by lay)) fun x' ⟨hP₁, _, hb⟩ => ⟨⟨_, hP₁.b⟩, by
        rw [show 34 = 32 + 2 from rfl, Proof.MlKem.bytesAt_add, S.lay.keepBytes hP₁.b (by layk),
          show pa x' (sc oSA) + BitVec.ofNat 64 32 = pa x' (sc (oSA + 32)) from off_add _ _ _, hP₁.pa rbx_cs, hb]⟩
  refine RelCT.seq (RelCT.postDep (taintRel [.rbx] (fun x y h => two_rbx h.1) (setIJ_taint _ (by omega) _ (by omega)))
    (F := F) (fun x y h => ⟨hF1 x h.1.sx, hF1 y h.1.sy⟩)
    (Q := fun x y => Two p x y ∧ bytesAt x.mem (pa x (sc oSA)) 34 = bytesAt y.mem (pa y (sc oSA)) 34)
    fun x y x' y' ⟨T, e32⟩ ⟨⟨_, hx⟩, bx⟩ ⟨⟨_, hy⟩, by'⟩ => ⟨T.post hx hy, by rw [bx, by', e32]⟩) ?_
  have ok := fun x (S : Site p x) => WP.mono (rejNttAt_ok (sd := sc oSA) (a := aP e) (sc_ok _ (by decide))
    (sc_ok _ (by simp only [oP]; omega)) (by lay) (by lay) (by lay) (by lay) (by lay) hP.rejNtt S)
    fun _ h => (⟨_, h.1.b⟩ : ∃ W, PostB x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1) (rejNttAt_tr (sc_ok _ (by decide)) (sc_ok _ (by simp only [oP]; omega))
      (by lay) (by lay) (by lay) (by lay) (by lay) hP.rejNtt (show Reg.rbx ∈ kgRegs by decide) (show Reg.rbx ∈ kgRegs by decide))
      fun x y h => ⟨ok x h.1.sx, ok y h.1.sy⟩)
    (mask_tr (j := e) (by omega) fun x y h => h.regs .rbx (by decide))

end VG.Proof.MlDsa.X86_64.KeyGen
