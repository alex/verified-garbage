import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp

/-!
# ML-DSA verification on AArch64: `w′₁`, row by row

With the entries `A'` of `Â` and `c = c0` as the samplers left them, and `x24`
their result `q` (`SC`): `ẑ[i] = NTT(z[i])` (`nttZ_vpiece`), `ĉ`
(`nttC_vpiece`), and each row `r` of `w′₁`, packed to `w1Encode(w′₁)`
(`row_vpiece`).
-/

namespace VG.Proof.MlDsa.AArch64.Verify

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv multiplyNTT polyAt natPolyAt coeffAt Reduced PolyIs NatPolyIs
  HintIs Bounds minBounds rejNTTPoly sampleInBall simpleBitPack d ofInt)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Proof.MlDsa.Verify (zHat dotAcc t1Hat wRow w1Row vT1 aSeed)

/-- Where row `r` of `w1Encode(w′₁)` goes. -/
abbrev rowP (p : Params) (r : Nat) : Ptr := sc (oP (p.k * p.ℓ + 0) + w1Len p * r)

/-- What the samplers gave: `q` whether they succeeded, `Â = A'` and `c = c0` if so. -/
def Gd (p : Params) (σ : State) (A' : Nat → Nat → Poly) (c0 : Poly) (q : Bool) : Prop :=
  (q = true → (∀ r < p.k, ∀ c < p.ℓ, ∃ b : Bounds, rejNTTPoly b.rejNTT (aSeed (vPk p σ) r c) = some (A' r c)) ∧
      ∃ b : Bounds, (sampleInBall p.τ b.ball (ctOf p σ)).map toRq = some c0) ∧
    (q = false → (∃ r < p.k, ∃ c < p.ℓ, rejNTTPoly minBounds.rejNTT (aSeed (vPk p σ) r c) = none) ∨
      (sampleInBall p.τ minBounds.ball (ctOf p σ)).map toRq = none)

/-- While computing: `ẑ[i]` for `i < j` (`z[i]` after), `ĉ` if `cn` (`c` if not),
and the rows of `w′₁` before `r` packed. -/
structure SC (p : Params) (σ : State) (h : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → Poly) (c0 : Poly)
    (q : Bool) (j : Nat) (cn : Bool) (r : Nat) (s : State) : Prop where
  vc : VC p σ s
  hh : hintOf p σ = some h
  hint : HintIs s.mem (pa s (hP p 0)) p.k h
  nok : normOk p σ p.ℓ
  gd : Gd p σ A' c0 q
  a : ∀ r' < p.k, ∀ c < p.ℓ, PolyIs s.mem (pa s (aP (p.ℓ * r' + c))) (A' r' c)
  z : ∀ i < p.ℓ, PolyIs s.mem (pa s (zP p i))
    (if i < j then zHat p (vSig p σ) i else toRq (zOf p σ i))
  c : PolyIs s.mem (pa s (cP p)) (if cn then ntt c0 else c0)
  rows : ∀ r' < r, bytesAt s.mem (pa s (rowP p r')) (w1Len p) =
    simpleBitPack (w1Row p (vPk p σ) (vSig p σ) A' (ntt c0) h r') (w1Max p)
  x24 : s.gpr .x24 = flag (q = true)

abbrev SCx (p : Params) (j : Nat) (cn : Bool) (r : Nat) (σ s : State) : Prop :=
  ∃ h A' c0 q, SC p σ h A' c0 q j cn r s

/-- A piece that writes `ws` keeps `SC`. -/
structure SCChk (p : Params) (r : Nat) (ws : List (Ptr × Nat)) : Prop where
  vc : vcChk p ws = true
  hint : keepB (vR p) (vW p) ws (hP p 0) (1024 * p.k) = true
  a : ∀ r' < p.k, ∀ c < p.ℓ, keepB (vR p) (vW p) ws (aP (p.ℓ * r' + c)) 1024 = true
  z : ∀ i < p.ℓ, keepB (vR p) (vW p) ws (zP p i) 1024 = true
  c : keepB (vR p) (vW p) ws (cP p) 1024 = true
  rows : ∀ r' < r, keepB (vR p) (vW p) ws (rowP p r') (w1Len p) = true

theorem ar_lt {p : Params} {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) : p.ℓ * r + c < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show r + 1 ≤ p.k by omega)
  rw [Nat.mul_succ, Nat.mul_comm p.ℓ p.k] at this
  omega

/-- Proves an `SCChk`. -/
syntax "scchk " term:max : tactic
macro_rules
  | `(tactic| scchk $hF) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr; have := ($hF).small
      rcases ($hF).wl with hw | hw <;> have hkw := ($hF).w1 <;> rw [hw] at hkw <;>
      refine ⟨?_, ?_, fun r' hr' c hc => ?_, ?_, ?_, ?_⟩ <;> intros <;>
      (try have := ar_lt hr' hc) <;> (try unfold VG.Proof.MlDsa.AArch64.Verify.vcChk) <;> vlay [hw]))

theorem SC.keep {p : Params} (hF : VFacts p) {S : Nat} {σ : State} (hp : vPre p S σ) {h : List (Vector Bool _)}
    {A' : Nat → Nat → Poly} {c0 : Poly} {q : Bool} {j : Nat} {cn : Bool} {r : Nat} {s s' : State}
    (hs : SC p σ h A' c0 q j cn r s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : SCChk p r ws)
    (h24 : s'.gpr .x24 = s.gpr .x24) : SC p σ h A' c0 q j cn r s' := by
  have L := hs.vc.lay hF hp
  exact ⟨hs.vc.step hF hp hP hc.vc, hs.hh, L.keepHint hP hc.hint hs.hint, hs.nok, hs.gd,
    fun r' hr' c hc' => L.keepPoly hP (hc.a r' hr' c hc') (hs.a r' hr' c hc'),
    fun i hi => L.keepPoly hP (hc.z i hi) (hs.z i hi), L.keepPoly hP hc.c hs.c,
    fun r' hr' => by rw [L.keepBytes hP (hc.rows r' hr')]; exact hs.rows r' hr', by rw [h24]; exact hs.x24⟩

/-! ## From the samplers -/

theorem seedOf_ar (p : Params) (σ : State) {r c : Nat} (hc : c < p.ℓ) :
    seedOf p σ (p.ℓ * r + c) = aSeed (vPk p σ) r c := by
  have hl : 0 < p.ℓ := by omega
  rw [seedOf, Nat.mul_add_div hl, Nat.div_eq_of_lt hc, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]

theorem vb_sc {p : Params} {σ s : State} (hs : VB p σ s) : SCx p 0 false 0 σ s := by
  obtain ⟨h, hh, hH⟩ := hs.vz.hint
  obtain ⟨q, hq, h1, h0⟩ := hs.ok
  refine ⟨h, fun r c => polyAt s.mem (pa s (aP (p.ℓ * r + c))), polyAt s.mem (pa s (cP p)), q,
    ⟨hs.vz.vc, hh, hH, hs.nok, ⟨fun hq' => ⟨fun r hr c hc => ?_, (h1 hq').2⟩, fun hq' => ?_⟩,
      fun r hr c hc => ⟨hs.red _ (ar_lt hr hc), rfl⟩, fun i hi => by rw [ifn (Nat.not_lt_zero _)]; exact hs.vz.z i hi,
      ⟨hs.redC, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _), hq⟩⟩
  · obtain ⟨b, hb⟩ := (h1 hq').1 _ (ar_lt hr hc)
    exact ⟨b, by rw [← seedOf_ar p σ hc]; exact hb⟩
  · rcases h0 hq' with ⟨e, he, hn⟩ | hn
    · have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega
      refine .inl ⟨e / p.ℓ, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he), e % p.ℓ, Nat.mod_lt _ hl, ?_⟩
      rw [← seedOf_ar p σ (Nat.mod_lt _ hl), Nat.div_add_mod]; exact hn
    · exact .inr hn

/-! ## The NTTs -/

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
include hP hF

theorem nttZ_vpiece {i : Nat} (hi : i < p.ℓ) :
    VPiece p S (SCx p i false 0) (SCx p (i + 1) false 0) (nttAt P (sc oSS) (zP p i)) := by
  have hc : ipChk (vR p) (vW p) (zP p i) (sc oSS) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; unfold ipChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs⟩ => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧
    Reduced x.mem (pa x (zP p i)) ∧ Reduced y.mem (pa y (zP p i)))
    (by unfold nttAt; exact ipAt_tr hP.ntt (vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ⟨vc_two hF p₁ p₂ pub h₁.vc h₂.vc,
      (h₁.z i hi).1, (h₂.z i hi).1⟩⟩
  have L := hs.vc.lay hF hp
  have hz := hs.z i hi
  rw [ifn (Nat.lt_irrefl _)] at hz
  unfold nttAt
  refine WP.mono (ipAt_ok hP.s64 hP.ntt L hc hz.1) fun s' ⟨hP', x', hq⟩ => ⟨h, A', c0, q, ?_⟩
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr
  refine ⟨hs.vc.step hF hp hP' (by unfold vcChk; vlay), hs.hh, L.keepHint hP' (by vlay) hs.hint, hs.nok, hs.gd,
    fun r' hr' c hc' => L.keepPoly hP' (by have := ar_lt hr' hc'; vlay) (hs.a r' hr' c hc'), fun i' hi' => ?_,
    L.keepPoly hP' (by vlay) hs.c, fun _ h => absurd h (Nat.not_lt_zero _), by rw [x']; exact hs.x24⟩
  rcases (by omega : i' < i ∨ i' = i ∨ i < i') with hlt | rfl | hgt
  · rw [ifp (by omega : i' < i + 1)]
    have := L.keepPoly hP' (by vlay) (hs.z i' hi')
    rwa [ifp hlt] at this
  · rw [ifp (Nat.lt_succ_self _), hP'.pa (show Reg.x28 ∈ bases by decide)]
    rw [hz.2] at hq
    exact hq
  · rw [ifn (by omega : ¬ i' < i + 1)]
    have := L.keepPoly hP' (by vlay) (hs.z i' hi')
    rwa [ifn (by omega : ¬ i' < i)] at this

theorem nttC_vpiece : VPiece p S (SCx p p.ℓ false 0) (SCx p p.ℓ true 0) (nttAt P (sc oSS) (cP p)) := by
  have hc : ipChk (vR p) (vW p) (cP p) (sc oSS) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; unfold ipChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs⟩ => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧
    Reduced x.mem (pa x (cP p)) ∧ Reduced y.mem (pa y (cP p)))
    (by unfold nttAt; exact ipAt_tr hP.ntt (vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ⟨vc_two hF p₁ p₂ pub h₁.vc h₂.vc, h₁.c.1, h₂.c.1⟩⟩
  have L := hs.vc.lay hF hp
  have hcc := hs.c
  simp only [Bool.false_eq_true, ↓reduceIte] at hcc
  unfold nttAt
  refine WP.mono (ipAt_ok hP.s64 hP.ntt L hc hcc.1) fun s' ⟨hP', x', hq⟩ => ⟨h, A', c0, q, ?_⟩
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr
  refine ⟨hs.vc.step hF hp hP' (by unfold vcChk; vlay), hs.hh, L.keepHint hP' (by vlay) hs.hint, hs.nok, hs.gd,
    fun r' hr' c hc' => L.keepPoly hP' (by have := ar_lt hr' hc'; vlay) (hs.a r' hr' c hc'),
    fun i hi => L.keepPoly hP' (by vlay) (hs.z i hi), ?_, fun _ h => absurd h (Nat.not_lt_zero _),
    by rw [x']; exact hs.x24⟩
  rw [hP'.pa (show Reg.x28 ∈ bases by decide), ifp rfl]
  rw [hcc.2] at hq
  exact hq

end

/-! ## A row -/

/-- In row `r`, with `f` holding of the temporaries. -/
abbrev RowI (p : Params) (r : Nat)
    (f : State → List (Vector Bool Spec.MlDsa.n) → (Nat → Nat → Poly) → Poly → State → Prop) (σ s : State) : Prop :=
  ∃ h A' c0 q, SC p σ h A' c0 q p.ℓ true r s ∧ f σ h A' c0 s

/-- `Σ_{s < j} Â[r, s] ẑ[s]` in `w′`. -/
abbrev wIs (p : Params) (σ : State) (r j : Nat) (A' : Nat → Nat → Poly) (s : State) : Prop :=
  PolyIs s.mem (pa s (wP p)) (dotAcc p (vSig p σ) A' r j)

/-- `Σₛ Â[r, s] ẑ[s]`. -/
abbrev rDot (p : Params) (σ : State) (A' : Nat → Nat → Poly) (r : Nat) : Poly := dotAcc p (vSig p σ) A' r p.ℓ
/-- `t₁[r] · 2ᵈ`. -/
abbrev rU (p : Params) (σ : State) (r : Nat) : Poly := (vT1 (vPk p σ) r).map fun c => ofInt (c * 2 ^ d : Nat)

theorem SC.zHat {p : Params} {σ : State} {h : List (Vector Bool _)} {A' : Nat → Nat → Poly} {c0 : Poly} {q : Bool}
    {r : Nat} {s : State} (hs : SC p σ h A' c0 q p.ℓ true r s) {c : Nat} (hc : c < p.ℓ) :
    PolyIs s.mem (pa s (zP p c)) (zHat p (vSig p σ) c) := by
  have := hs.z c hc; rwa [ifp hc] at this

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) {r : Nat} (hr : r < p.k)
include hP hF hr

omit hP in
theorem mulW_chk {c : Nat} (hc : c < p.ℓ) : mulChk (vR p) (vW p) (wP p) (aP (p.ℓ * r + c)) (zP p c) = true := by
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; have := ar_lt hr hc
  unfold mulChk; vlay

end

theorem rowI_two {p : Params} (hF : VFacts p) {S r : Nat} {f : State → List (Vector Bool Spec.MlDsa.n) →
    (Nat → Nat → Poly) → Poly → State → Prop} {σ₁ σ₂ x y : State} (p₁ : vPre p S σ₁) (p₂ : vPre p S σ₂)
    (pub : vPub p S σ₁ σ₂) (h₁ : RowI p r f σ₁ x) (h₂ : RowI p r f σ₂ y) : VTwo p S x y :=
  let ⟨_, _, _, _, a, _⟩ := h₁; let ⟨_, _, _, _, b, _⟩ := h₂; vc_two hF p₁ p₂ pub a.vc b.vc

theorem hintRow_pa (p : Params) (s : State) (r : Nat) :
    pa s (hP p r) = pa s (hP p 0) + BitVec.ofNat 64 (1024 * r) := by
  have e : oP (p.k * p.ℓ + (1 + r)) = oP (p.k * p.ℓ + (1 + 0)) + 1024 * r := by simp only [oP]; omega
  rw [show pa s (hP p r) = s.gpr .x28 + BitVec.ofNat 64 (oP (p.k * p.ℓ + (1 + r))) from rfl,
    show pa s (hP p 0) = s.gpr .x28 + BitVec.ofNat 64 (oP (p.k * p.ℓ + (1 + 0))) from rfl, e, BitVec.ofNat_add,
    BitVec.add_assoc]

/-- The temporaries of a row, facts about them. -/
abbrev F1 (p : Params) (r j : Nat) (σ : State) (_ : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → Poly)
    (_ : Poly) (s : State) : Prop := wIs p σ r j A' s
abbrev F3 (p : Params) (r : Nat) (σ : State) (_ : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → Poly)
    (_ : Poly) (s : State) : Prop := wIs p σ r p.ℓ A' s ∧ PolyIs s.mem (pa s (tmP p)) (rU p σ r)
abbrev F4 (p : Params) (r : Nat) (σ : State) (_ : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → Poly)
    (_ : Poly) (s : State) : Prop := wIs p σ r p.ℓ A' s ∧ PolyIs s.mem (pa s (tmP p)) (ntt (rU p σ r))
abbrev F5 (p : Params) (r : Nat) (σ : State) (_ : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → Poly)
    (c0 : Poly) (s : State) : Prop :=
  wIs p σ r p.ℓ A' s ∧ PolyIs s.mem (pa s (tm2P p)) (multiplyNTT (ntt c0) (t1Hat (vPk p σ) r))
abbrev F6 (p : Params) (r : Nat) (σ : State) (_ : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → Poly)
    (c0 : Poly) (s : State) : Prop :=
  PolyIs s.mem (pa s (wP p)) (Spec.MlDsa.sub (rDot p σ A' r) (multiplyNTT (ntt c0) (t1Hat (vPk p σ) r)))
abbrev F7 (p : Params) (r : Nat) (σ : State) (_ : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → Poly)
    (c0 : Poly) (s : State) : Prop := PolyIs s.mem (pa s (wP p)) (wRow p (vPk p σ) (vSig p σ) A' (ntt c0) r)
abbrev F8 (p : Params) (r : Nat) (σ : State) (h : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → Poly)
    (c0 : Poly) (s : State) : Prop := NatPolyIs s.mem (pa s (w1P p)) (w1Row p (vPk p σ) (vSig p σ) A' (ntt c0) h r)

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) {r : Nat} (hr : r < p.k)
include hP hF hr

theorem dot0_vpiece : VPiece p S (SCx p p.ℓ true r) (RowI p r (F1 p r 1)) (mulAt P (wP p) (aP (p.ℓ * r)) (zP p 0)) := by
  have hl := hF.l
  have hc := mulW_chk hF hr (c := 0) (by omega)
  rw [Nat.add_zero] at hc
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs⟩ => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧
    (Reduced x.mem (pa x (aP (p.ℓ * r))) ∧ Reduced x.mem (pa x (zP p 0))) ∧
    (Reduced y.mem (pa y (aP (p.ℓ * r))) ∧ Reduced y.mem (pa y (zP p 0))))
    (mulAt_tr hP.mul (vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ⟨vc_two hF p₁ p₂ pub h₁.vc h₂.vc, ?_, ?_⟩⟩
  · have L := hs.vc.lay hF hp
    have hA := hs.a r hr 0 (by omega)
    rw [Nat.add_zero] at hA
    have hZ := hs.zHat (c := 0) (by omega)
    refine WP.mono (mulAt_ok hP.s64 hP.mul L hc hA.1 hZ.1) fun s' ⟨hP', x', hq⟩ =>
      ⟨h, A', c0, q, hs.keep hF hp hP' (by scchk hF) x', ?_⟩
    rw [hA.2, hZ.2] at hq
    show PolyIs _ _ _
    rw [hP'.pa (show Reg.x28 ∈ bases by decide)]
    simp only [dotAcc, Proof.MlDsa.Verify.add_zero_left]
    exact hq
  · have := h₁.a r hr 0 (by omega); rw [Nat.add_zero] at this; exact ⟨this.1, (h₁.zHat (c := 0) (by omega)).1⟩
  · have := h₂.a r hr 0 (by omega); rw [Nat.add_zero] at this; exact ⟨this.1, (h₂.zHat (c := 0) (by omega)).1⟩

theorem dotS_vpiece {j : Nat} (hj : j < p.ℓ) : VPiece p S (RowI p r (F1 p r j)) (RowI p r (F1 p r (j + 1)))
    (mulAddAt P (wP p) (aP (p.ℓ * r + j)) (zP p j)) := by
  have hc := mulW_chk hF hr hj
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw⟩ => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧
    (Reduced x.mem (pa x (wP p)) ∧ Reduced x.mem (pa x (aP (p.ℓ * r + j))) ∧ Reduced x.mem (pa x (zP p j))) ∧
    (Reduced y.mem (pa y (wP p)) ∧ Reduced y.mem (pa y (aP (p.ℓ * r + j))) ∧ Reduced y.mem (pa y (zP p j))))
    (mulAddAt_tr hP.mulAdd (vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁, w₁⟩ ⟨_, _, _, _, h₂, w₂⟩ => ⟨vc_two hF p₁ p₂ pub h₁.vc h₂.vc,
      ⟨w₁.1, (h₁.a r hr j hj).1, (h₁.zHat hj).1⟩, ⟨w₂.1, (h₂.a r hr j hj).1, (h₂.zHat hj).1⟩⟩⟩
  have L := hs.vc.lay hF hp
  have hA := hs.a r hr j hj
  have hZ := hs.zHat hj
  refine WP.mono (mulAddAt_ok hP.s64 hP.mulAdd L hc hw.1 hA.1 hZ.1) fun s' ⟨hP', x', hq⟩ =>
    ⟨h, A', c0, q, hs.keep hF hp hP' (by scchk hF) x', ?_⟩
  rw [hA.2, hZ.2, hw.2] at hq
  show PolyIs _ _ _
  rw [hP'.pa (show Reg.x28 ∈ bases by decide)]
  exact hq

theorem dot_vpiece : VPiece p S (SCx p p.ℓ true r) (RowI p r (F1 p r p.ℓ)) (dot P p r) := by
  have hl := hF.l
  unfold dot
  refine (dot0_vpiece hP hF hr).seq ?_
  refine VPiece.mono (VPiece.seqR (I := fun j => RowI p r (F1 p r j)) (p.ℓ - 1) 1
    fun j h1 h2 => dotS_vpiece hP hF hr (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h

theorem t1_vpiece : VPiece p S (RowI p r (F1 p r p.ℓ)) (RowI p r (F3 p r)) (unpackT1At P (.x25, 32 + 320 * r) (tmP p)) := by
  have hc : rwChk (vR p) (vW p) (.x25, 32 + 320 * r) 320 (tmP p) 1024 = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; have := hF.pk; unfold rwChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw⟩ => ?_, vrel_of (Q := VTwo p S)
    (t1At_tr hP.unpackT1 (vOk p) hc fun x y h => ⟨h.lx, h.ly, h.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => rowI_two hF p₁ p₂ pub h₁ h₂⟩
  have L := hs.vc.lay hF hp
  refine WP.mono (t1At_ok hP.s64 hP.unpackT1 L hc) fun s' ⟨hP', x', hq⟩ =>
    ⟨h, A', c0, q, hs.keep hF hp hP' (by scchk hF) x', L.keepPoly hP' (by
      have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; vlay) hw, ?_⟩
  rw [hs.vc.pkSlice (by rw [hF.pk]; omega)] at hq
  rw [hP'.pa (show Reg.x28 ∈ bases by decide)]
  exact hq

theorem nttT_vpiece : VPiece p S (RowI p r (F3 p r)) (RowI p r (F4 p r)) (nttAt P (sc oSS) (tmP p)) := by
  have hc : ipChk (vR p) (vW p) (tmP p) (sc oSS) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; unfold ipChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw, ht⟩ => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧
    Reduced x.mem (pa x (tmP p)) ∧ Reduced y.mem (pa y (tmP p)))
    (by unfold nttAt; exact ipAt_tr hP.ntt (vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨rowI_two hF p₁ p₂ pub h₁ h₂, ?_, ?_⟩⟩
  · have L := hs.vc.lay hF hp
    unfold nttAt
    refine WP.mono (ipAt_ok hP.s64 hP.ntt L hc ht.1) fun s' ⟨hP', x', hq⟩ =>
      ⟨h, A', c0, q, hs.keep hF hp hP' (by scchk hF) x', L.keepPoly hP' (by
        have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; vlay) hw, ?_⟩
    rw [ht.2] at hq
    rw [hP'.pa (show Reg.x28 ∈ bases by decide)]
    exact hq
  · obtain ⟨_, _, _, _, _, _, t⟩ := h₁; exact t.1
  · obtain ⟨_, _, _, _, _, _, t⟩ := h₂; exact t.1

theorem mulT_vpiece : VPiece p S (RowI p r (F4 p r)) (RowI p r (F5 p r)) (mulAt P (tm2P p) (cP p) (tmP p)) := by
  have hc : mulChk (vR p) (vW p) (tm2P p) (cP p) (tmP p) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; unfold mulChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw, ht⟩ => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧
    (Reduced x.mem (pa x (cP p)) ∧ Reduced x.mem (pa x (tmP p))) ∧
    (Reduced y.mem (pa y (cP p)) ∧ Reduced y.mem (pa y (tmP p))))
    (mulAt_tr hP.mul (vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨rowI_two hF p₁ p₂ pub h₁ h₂, ?_, ?_⟩⟩
  · have L := hs.vc.lay hF hp
    have hC := hs.c
    rw [ifp rfl] at hC
    refine WP.mono (mulAt_ok hP.s64 hP.mul L hc hC.1 ht.1) fun s' ⟨hP', x', hq⟩ =>
      ⟨h, A', c0, q, hs.keep hF hp hP' (by scchk hF) x', L.keepPoly hP' (by
        have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; vlay) hw, ?_⟩
    rw [hC.2, ht.2] at hq
    rw [hP'.pa (show Reg.x28 ∈ bases by decide)]
    exact hq
  · obtain ⟨_, _, _, _, hs, _, t⟩ := h₁; exact ⟨hs.c.1, t.1⟩
  · obtain ⟨_, _, _, _, hs, _, t⟩ := h₂; exact ⟨hs.c.1, t.1⟩

theorem sub_vpiece : VPiece p S (RowI p r (F5 p r)) (RowI p r (F6 p r)) (subAt P (wP p) (tm2P p)) := by
  have hc : accChk (vR p) (vW p) (wP p) (tm2P p) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; unfold accChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw, ht⟩ => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧
    (Reduced x.mem (pa x (wP p)) ∧ Reduced x.mem (pa x (tm2P p))) ∧
    (Reduced y.mem (pa y (wP p)) ∧ Reduced y.mem (pa y (tm2P p))))
    (by unfold subAt; exact accAt_tr (op := Spec.MlDsa.sub) hP.sub (vOk p) hc fun x y h =>
      ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨rowI_two hF p₁ p₂ pub h₁ h₂, ?_, ?_⟩⟩
  · have L := hs.vc.lay hF hp
    unfold subAt
    refine WP.mono (accAt_ok (op := Spec.MlDsa.sub) hP.s64 hP.sub L hc hw.1 ht.1) fun s' ⟨hP', x', hq⟩ =>
      ⟨h, A', c0, q, hs.keep hF hp hP' (by scchk hF) x', ?_⟩
    rw [hw.2, ht.2] at hq
    show PolyIs _ _ _
    rw [hP'.pa (show Reg.x28 ∈ bases by decide)]
    exact hq
  · obtain ⟨_, _, _, _, _, w, t⟩ := h₁; exact ⟨w.1, t.1⟩
  · obtain ⟨_, _, _, _, _, w, t⟩ := h₂; exact ⟨w.1, t.1⟩

theorem inv_vpiece : VPiece p S (RowI p r (F6 p r)) (RowI p r (F7 p r)) (invNttAt P (sc oSS) (wP p)) := by
  have hc : ipChk (vR p) (vW p) (wP p) (sc oSS) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; unfold ipChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw⟩ => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧
    Reduced x.mem (pa x (wP p)) ∧ Reduced y.mem (pa y (wP p)))
    (by unfold invNttAt; exact ipAt_tr hP.invNtt (vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨rowI_two hF p₁ p₂ pub h₁ h₂, ?_, ?_⟩⟩
  · have L := hs.vc.lay hF hp
    unfold invNttAt
    refine WP.mono (ipAt_ok hP.s64 hP.invNtt L hc hw.1) fun s' ⟨hP', x', hq⟩ =>
      ⟨h, A', c0, q, hs.keep hF hp hP' (by scchk hF) x', ?_⟩
    rw [hw.2] at hq
    show PolyIs _ _ _
    rw [hP'.pa (show Reg.x28 ∈ bases by decide)]
    exact hq
  · obtain ⟨_, _, _, _, _, w⟩ := h₁; exact w.1
  · obtain ⟨_, _, _, _, _, w⟩ := h₂; exact w.1

theorem uh_vpiece : VPiece p S (RowI p r (F7 p r)) (RowI p r (F8 p r)) (useHintAt P (VG.Impl.MlDsa.AArch64.Verify.hP p r) (wP p) p.γ₂ (w1P p)) := by
  have hc : useHintChk (vR p) (vW p) (VG.Impl.MlDsa.AArch64.Verify.hP p r) (wP p) (w1P p) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; unfold useHintChk; vlay
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw⟩ => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧
    Reduced x.mem (pa x (wP p)) ∧ Reduced y.mem (pa y (wP p)))
    (useHintAt_tr hP.useHint (vOk p) hc hF.g2.1 fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨rowI_two hF p₁ p₂ pub h₁ h₂, ?_, ?_⟩⟩
  · have L := hs.vc.lay hF hp
    refine WP.mono (useHintAt_ok hP.s64 hP.useHint L hc hF.g2.1 hw.1) fun s' ⟨hP', x', hq⟩ =>
      ⟨h, A', c0, q, hs.keep hF hp hP' (by scchk hF) x', ?_⟩
    rw [hintRow_pa p s r, Proof.MlDsa.Verify.hintAt_row hs.hint hr, hw.2] at hq
    show natPolyAt _ _ = _
    rw [hP'.pa (show Reg.x28 ∈ bases by decide)]
    exact hq
  · obtain ⟨_, _, _, _, _, w⟩ := h₁; exact w.1
  · obtain ⟨_, _, _, _, _, w⟩ := h₂; exact w.1

omit hP hr in
theorem w1_bound {m : Mem} {a : Addr} {σ : State} {h : List (Vector Bool Spec.MlDsa.n)} {A' : Nat → Nat → Poly}
    {c0 : Poly} {r : Nat} (hq : NatPolyIs m a (w1Row p (vPk p σ) (vSig p σ) A' (ntt c0) h r)) :
    ∀ i < 256, (coeffAt m a i).toNat ≤ w1Max p := fun i hi => by
  have := congrArg (·[i]'hi) hq
  simp only [natPolyAt, Vector.getElem_ofFn, w1Row, Vector.getElem_zipWith] at this
  rw [this, hF.g2.2]
  exact Proof.MlDsa.Verify.useHint_le hF.g2.1 _ _

theorem sbpR_vpiece : VPiece p S (RowI p r (F8 p r)) (SCx p p.ℓ true (r + 1))
    (simpleBitPackAt P (w1P p) (w1Max p) (rowP p r) (w1Len p)) := by
  have hc : rwChk (vR p) (vW p) (w1P p) 1024 (rowP p r) (w1Len p) = true := by
    have := hF.k; have := hF.l; have := hF.kl; have := hF.scr
    rcases hF.wl with hw | hw <;> have hkw := hF.w1 <;> rw [hw] at hkw <;> (unfold rwChk; vlay [hw])
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hw⟩ => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧
    (∀ i < 256, (coeffAt x.mem (pa x (w1P p)) i).toNat ≤ w1Max p) ∧
    (∀ i < 256, (coeffAt y.mem (pa y (w1P p)) i).toNat ≤ w1Max p))
    (sbpAt_tr hP.simpleBitPack (vOk p) hc hF.sbp fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨rowI_two hF p₁ p₂ pub h₁ h₂, ?_, ?_⟩⟩
  · have L := hs.vc.lay hF hp
    refine WP.mono (sbpAt_ok hP.s64 hP.simpleBitPack L hc hF.sbp (w1_bound hF hw)) fun s' ⟨hP', x', hq⟩ => ?_
    have hs' := hs.keep hF hp hP' (by scchk hF) x'
    refine ⟨h, A', c0, q, ⟨hs'.vc, hs'.hh, hs'.hint, hs'.nok, hs'.gd, hs'.a, hs'.z, hs'.c, fun r' hr' => ?_,
      hs'.x24⟩⟩
    rcases (by omega : r' < r ∨ r' = r) with hlt | rfl
    · exact hs'.rows r' hlt
    · rw [hP'.pa (show Reg.x28 ∈ bases by decide), hq, hw]
  · obtain ⟨_, _, _, _, _, w⟩ := h₁; exact w1_bound hF w
  · obtain ⟨_, _, _, _, _, w⟩ := h₂; exact w1_bound hF w

theorem row_vpiece : VPiece p S (SCx p p.ℓ true r) (SCx p p.ℓ true (r + 1))
    (VG.Impl.MlDsa.AArch64.Verify.row P p r) := by
  unfold VG.Impl.MlDsa.AArch64.Verify.row
  exact (dot_vpiece hP hF hr).seq ((t1_vpiece hP hF hr).seq ((nttT_vpiece hP hF hr).seq
    ((mulT_vpiece hP hF hr).seq ((sub_vpiece hP hF hr).seq ((inv_vpiece hP hF hr).seq
      ((uh_vpiece hP hF hr).seq (sbpR_vpiece hP hF hr)))))))

end

end VG.Proof.MlDsa.AArch64.Verify
