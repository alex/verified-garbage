import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.StageA
import VerifiedGarbage.Proof.MlDsa.Verify.Final

/-!
# ML-DSA verification on x86-64: `w′₁`, row by row

Untrusted: everything here is checked by Lean. With the entries `A'` of
`Â` and `ĉ = cH` as the samplers left them: `ẑ[i] = NTT(z[i])`
(`nttZ_ok`), `ĉ` (`nttC_ok`), and each row `r` of `w′₁`, packed to
`B + r · 32 bitlen b` (`row_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt vRho aSeed zHat dotAcc t1Hat wRow w1Row vT1 add_zero_left hintAt_row useHint_le)

/-- While computing, with the hint `h`, `Â = A'`, the result so far `Q`:
`ẑ[i]` for `i < j` (`z[i]` after), `ĉ` or `c` at `C` (`cH`), and the rows
of `w′₁` before `r` packed. -/
structure SC (p : Params) (h : List (Vector Bool n)) (A' : Nat → Nat → Poly) (Q : Prop) [Decidable Q]
    (j : Nat) (cH : Poly) (r : Nat) (σ st : State) : Prop where
  t : T p σ st
  hint : HintIs st.mem (pa st (pH 0)) p.k h
  a : ∀ r' < p.k, ∀ c < p.ℓ, PolyIs st.mem (pa st (pA r' c)) (A' r' c)
  z : ∀ i < p.ℓ, PolyIs st.mem (pa st (pZ i)) (if i < j then zHat p (vSig p σ) i else toRq (vZ p (vSig p σ) i))
  c : PolyIs st.mem (pa st pC) cH
  rows : ∀ r' < r, bytesAt st.mem (pa st (sc (oB + w1Len p * r'))) (w1Len p) =
    simpleBitPack (w1Row p (vPk p σ) (vSig p σ) A' cH h r') (w1Max p)
  r15 : st.gpr .r15 = flag Q

/-- What a piece writing `ws` keeps of `SC`: `T`, the hint, `Â` and `z[i]`
but `z[ex]`, but for `C` and the rows. -/
def keepC (p : Params) (ws : List (Ptr × Nat)) (ex : Nat) : Bool :=
  tChk p ws && keepB (vB p) ws (pH 0) (1024 * p.k) &&
    (List.range p.ℓ).all (fun i => i == ex || keepB (vB p) ws (pZ i) 1024) &&
    (List.range p.k).all (fun r => (List.range p.ℓ).all fun c => keepB (vB p) ws (pA r c) 1024)

theorem keepC_spec {p : Params} {ws : List (Ptr × Nat)} {ex : Nat} (h : keepC p ws ex = true) :
    tChk p ws = true ∧ keepB (vB p) ws (pH 0) (1024 * p.k) = true ∧
      (∀ i < p.ℓ, i ≠ ex → keepB (vB p) ws (pZ i) 1024 = true) ∧
      ∀ r < p.k, ∀ c < p.ℓ, keepB (vB p) ws (pA r c) 1024 = true := by
  simp only [keepC, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, fun i hi hne => (h.1.2 i hi).resolve_left hne, h.2⟩

/-- The facts about the parameters the NTTs need. -/
def nttChk (p : Params) : Bool :=
  (List.range p.ℓ).all (fun i => ipChk (vB p) (vW p) (pZ i) && keepC p [(pZ i, 1024), (sc oSS, 1024)] i &&
    keepB (vB p) [(pZ i, 1024), (sc oSS, 1024)] pC 1024) &&
  ipChk (vB p) (vW p) pC && keepC p [(pC, 1024), (sc oSS, 1024)] 100

theorem nttChk_all : ∀ p ∈ params, nttChk p = true := by decide

theorem nttZ_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
    {i : Nat} (hi : i < p.ℓ) {s : State} (hs : SC p h A' Q i cH 0 σ s) :
    WP isa (nttAt P (pZ i)) s (SC p h A' Q (i + 1) cH 0 σ) := by
  have hc := nttChk_all p hp
  simp only [nttChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := hc.1.1 i hi
  obtain ⟨tk, hH, hZ, hA⟩ := keepC_spec c2
  have L := hs.t.lay hp hv
  refine WP.mono (ipAt_ok C.ntt L c1 (by have := hs.z i hi; rw [ifn (Nat.lt_irrefl _)] at this; exact this.1))
    fun s' ⟨hP, h15, hq⟩ => ?_
  refine ⟨hs.t.step hp hv hP tk, L.keepHint hP hH hs.hint, fun r' hr' c hc' => L.keepPoly hP (hA r' hr' c hc')
    (hs.a r' hr' c hc'), fun i' hi' => ?_, L.keepPoly hP c3 hs.c, fun _ h => absurd h (Nat.not_lt_zero _),
    by rw [h15]; exact hs.r15⟩
  rcases (by omega : i' < i ∨ i' = i ∨ i < i') with hlt | rfl | hgt
  · rw [ifp (by omega : i' < i + 1)]
    have := L.keepPoly hP (hZ i' hi' (by omega)) (hs.z i' hi')
    rwa [ifp hlt] at this
  · rw [ifp (Nat.lt_succ_self _), hP.pa (show Reg.rbx ∈ bases by decide)]
    have := (hs.z i' hi').2
    rw [ifn (Nat.lt_irrefl _)] at this
    rw [this] at hq
    exact hq
  · rw [ifn (by omega : ¬ i' < i + 1)]
    have := L.keepPoly hP (hZ i' hi' (by omega)) (hs.z i' hi')
    rwa [ifn (by omega : ¬ i' < i)] at this

theorem nttC_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
    {s : State} (hs : SC p h A' Q p.ℓ cH 0 σ s) :
    WP isa (nttAt P pC) s (SC p h A' Q p.ℓ (ntt cH) 0 σ) := by
  have hc := nttChk_all p hp
  simp only [nttChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨_, c1⟩, c2⟩ := hc
  obtain ⟨tk, hH, hZ, hA⟩ := keepC_spec c2
  have L := hs.t.lay hp hv
  refine WP.mono (ipAt_ok C.ntt L c1 hs.c.1) fun s' ⟨hP, h15, hq⟩ => ?_
  refine ⟨hs.t.step hp hv hP tk, L.keepHint hP hH hs.hint, fun r' hr' c hc' => L.keepPoly hP (hA r' hr' c hc')
    (hs.a r' hr' c hc'), fun i hi => L.keepPoly hP (hZ i hi (by have := kl_le p hp; omega)) (hs.z i hi), ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), by rw [h15]; exact hs.r15⟩
  rw [hP.pa (show Reg.rbx ∈ bases by decide), ← hs.c.2]
  exact hq


/-! ## A row -/

/-- What row `r` writes. -/
abbrev wsR (p : Params) (r : Nat) : List (Ptr × Nat) :=
  [(pW, 1024), (pT, 1024), (sc oSS, 1024), (pT2, 1024), (pW1, 1024), (sc (oB + w1Len p * r), w1Len p)]

/-- The facts about the parameters row `r` needs. -/
def rowChk (p : Params) (r : Nat) : Bool :=
  (List.range p.ℓ).all (fun c => mulChk (vB p) (vW p) pW (pA r c) (pZ c)) &&
    t1Chk (vB p) (vW p) (.rbp, 32 + 320 * r) pT && decide (32 + 320 * r + 320 ≤ p.pkLen) &&
    ipChk (vB p) (vW p) pT && ipChk (vB p) (vW p) pW && mulChk (vB p) (vW p) pT2 pC pT &&
    subChk (vB p) (vW p) pW pT2 && uhChk (vB p) (vW p) (pH r) pW pW1 && decide (p.γ₂ ∈ gamma2s) &&
    sbpChk (vB p) (vW p) pW1 (sc (oB + w1Len p * r)) (w1Len p) && decide (w1Max p ∈ simpleBitPackBounds) &&
    decide (w1Len p = 32 * bitlen (w1Max p)) && keepC p (wsR p r) 100 && keepB (vB p) (wsR p r) pC 1024 &&
    (List.range r).all (fun r' => keepB (vB p) (wsR p r) (sc (oB + w1Len p * r')) (w1Len p)) &&
    keepB (vB p) [(pT, 1024), (sc oSS, 1024), (pT2, 1024)] pW 1024 && decide (1 ≤ p.ℓ) &&
    decide (w1Max p = (q - 1) / (2 * p.γ₂) - 1)

theorem rowChk_all : ∀ p ∈ params, ∀ r < p.k, rowChk p r = true := by decide

theorem hintRow_pa (s : State) (r : Nat) : pa s (pH r) = pa s (pH 0) + BitVec.ofNat 64 (1024 * r) := by
  simp only [pa, oP]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_zero, Nat.add_zero]

theorem wsR_bases (p : Params) (r : Nat) : ∀ w ∈ wsR p r, w.1.1 ∈ bases := by
  intro w hw
  simp only [wsR, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (show Reg.rbx ∈ bases by decide)

/-- `rowChk`, piece by piece. -/
structure RowC (p : Params) (r : Nat) : Prop where
  mul : ∀ c < p.ℓ, mulChk (vB p) (vW p) pW (pA r c) (pZ c) = true
  t1 : t1Chk (vB p) (vW p) (.rbp, 32 + 320 * r) pT = true
  pk : 32 + 320 * r + 320 ≤ p.pkLen
  ipT : ipChk (vB p) (vW p) pT = true
  ipW : ipChk (vB p) (vW p) pW = true
  mulT : mulChk (vB p) (vW p) pT2 pC pT = true
  sub : subChk (vB p) (vW p) pW pT2 = true
  uh : uhChk (vB p) (vW p) (pH r) pW pW1 = true
  g2 : p.γ₂ ∈ gamma2s
  sbp : sbpChk (vB p) (vW p) pW1 (sc (oB + w1Len p * r)) (w1Len p) = true
  sbpB : w1Max p ∈ simpleBitPackBounds
  len : w1Len p = 32 * bitlen (w1Max p)
  keep : keepC p (wsR p r) 100 = true
  keepC' : keepB (vB p) (wsR p r) pC 1024 = true
  rows : ∀ r' < r, keepB (vB p) (wsR p r) (sc (oB + w1Len p * r')) (w1Len p) = true
  keepW : keepB (vB p) [(pT, 1024), (sc oSS, 1024), (pT2, 1024)] pW 1024 = true
  l1 : 1 ≤ p.ℓ
  max : w1Max p = (q - 1) / (2 * p.γ₂) - 1

theorem rowC {p : Params} (hp : p ∈ params) {r : Nat} (hr : r < p.k) : RowC p r := by
  have hc := rowChk_all p hp r hr
  simp only [rowChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩, c15⟩, c16⟩,
    c17⟩, c18⟩ := hc
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩

theorem wsR_mem (p : Params) (r : Nat) :
    (pW, 1024) ∈ wsR p r ∧ (pT, 1024) ∈ wsR p r ∧ (sc oSS, 1024) ∈ wsR p r ∧ (pT2, 1024) ∈ wsR p r ∧
      (pW1, 1024) ∈ wsR p r ∧ (sc (oB + w1Len p * r), w1Len p) ∈ wsR p r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wsR, List.mem_cons, true_or, or_true]

theorem sub1 {α : Type} {x : α} {l : List α} (h : x ∈ l) : ∀ w ∈ [x], w ∈ l := fun _ hw => by
  rw [List.mem_singleton.mp hw]; exact h

theorem sub2 {α : Type} {x y : α} {l : List α} (h : x ∈ l) (h' : y ∈ l) : ∀ w ∈ [x, y], w ∈ l := fun _ hw => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  exacts [h, h']

theorem PPostB.accR {p : Params} {r : Nat} {s s₁ s₂ : State} {ws : List (Ptr × Nat)} (h₁ : PPostB s s₁ (wsR p r))
    (h₂ : PPostB s₁ s₂ ws) (hw : ∀ w ∈ ws, w ∈ wsR p r) : PPostB s s₂ (wsR p r) :=
  h₁.trans h₂ (fun w hw' => wsR_bases p r w (hw w hw')) (fun _ h => h) hw

theorem pa_rbx {s s' : State} {W : List Region} (hP : PostB s s' W) (o : Nat) : pa s' (.rbx, o) = pa s (.rbx, o) :=
  hP.pa (show Reg.rbx ∈ bases by decide)

theorem dot_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
    {r : Nat} (hr : r < p.k) {s : State} (hs : SC p h A' Q p.ℓ cH r σ s) :
    WP isa (dot P p r) s fun s' => PPostB s s' [(pW, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (pa s pW) (dotAcc p (vSig p σ) A' r p.ℓ) := by
  have R := rowC hp hr
  have L := hs.t.lay hp hv
  obtain ⟨_, _, hZ, hA⟩ := keepC_spec R.keep
  have hz : ∀ c < p.ℓ, PolyIs s.mem (pa s (pZ c)) (zHat p (vSig p σ) c) := fun c hc => by
    have := hs.z c hc; rwa [ifp hc] at this
  have mW := (wsR_mem p r).1
  unfold dot
  refine WP.seq (WP.mono (mulAt_ok C.mul L (R.mul 0 R.l1) (hs.a r hr 0 R.l1).1 (hz 0 R.l1).1)
    fun s₁ ⟨hP₁, e₁, hq₁⟩ => ?_)
  rw [(hs.a r hr 0 R.l1).2, (hz 0 R.l1).2] at hq₁
  refine WP.mono (seqR_ok (I := fun j st => PPostB s st [(pW, 1024)] ∧ st.gpr .r15 = s.gpr .r15 ∧
    PolyIs st.mem (pa s pW) (dotAcc p (vSig p σ) A' r j)) (p.ℓ - 1) 1 (fun k hk hk' st ⟨hP, e, hW⟩ => ?_) s₁
    ⟨hP₁, e₁, by simp only [dotAcc, add_zero_left]; exact hq₁⟩) fun st hst => ?_
  · have hk'' : k < p.ℓ := by omega
    have H := hP.mono (sub1 mW)
    have ew : pa st pW = pa s pW := pa_rbx hP _
    refine WP.mono (mulAddAt_ok C.mulAdd (L.post hP) (R.mul k hk'') (by rw [ew]; exact hW.1)
      (L.keepRed H (hA r hr k hk'') (hs.a r hr k hk'').1)
      (L.keepRed H (hZ k hk'' (by have := kl_le p hp; omega)) (hz k hk'').1)) fun s' ⟨hP', e', hq'⟩ => ?_
    rw [ew, hW.2, L.keepPolyAt H (hA r hr k hk''), (hs.a r hr k hk'').2,
      L.keepPolyAt H (hZ k hk'' (by have := kl_le p hp; omega)), (hz k hk'').2] at hq'
    exact ⟨hP.trans hP' (fun w hw => by rw [List.mem_singleton.mp hw]; decide) (fun _ h => h) (fun _ h => h), e'.trans e, hq'⟩
  · rw [show 1 + (p.ℓ - 1) = p.ℓ by have := R.l1; omega] at hst
    exact hst

theorem row_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
    {r : Nat} (hr : r < p.k) {s : State} (hs : SC p h A' Q p.ℓ cH r σ s) :
    WP isa (row P p r) s (SC p h A' Q p.ℓ cH (r + 1) σ) := by
  have R := rowC hp hr
  have L := hs.t.lay hp hv
  obtain ⟨tk, hH, hZ, hA⟩ := keepC_spec R.keep
  obtain ⟨mW, mT, mS, mT2, mW1, mB⟩ := wsR_mem p r
  unfold row
  refine WP.seq (WP.mono (dot_ok C hp hv hr hs) fun s₁ ⟨hP₁, e₁, hq₁⟩ => ?_)
  have H₁ := hP₁.mono (sub1 mW)
  refine WP.seq (WP.mono (unpackT1At_ok C.unpackT1 (L.post H₁) R.t1) fun s₂ ⟨hP₂, e₂, hq₂⟩ => ?_)
  rw [(hs.t.step hp hv H₁ tk).pkSlice R.pk] at hq₂
  have H₂ := H₁.accR hP₂ (sub1 mT)
  have a₂ : pa s₂ pT = pa s₁ pT := pa_rbx hP₂ _
  refine WP.seq (WP.mono (ipAt_ok C.ntt (L.post H₂) R.ipT (by rw [a₂]; exact hq₂.1)) fun s₃ ⟨hP₃, e₃, hq₃⟩ => ?_)
  rw [a₂, hq₂.2] at hq₃
  have H₃ := H₂.accR hP₃ (sub2 mT mS)
  have hC₃ := L.keepPoly H₃ R.keepC' hs.c
  have a₃ : pa s₃ pT = pa s₁ pT := (pa_rbx hP₃ _).trans a₂
  refine WP.seq (WP.mono (mulAt_ok C.mul (L.post H₃) R.mulT hC₃.1 (by rw [a₃]; exact hq₃.1))
    fun s₄ ⟨hP₄, e₄, hq₄⟩ => ?_)
  rw [hC₃.2, a₃, hq₃.2] at hq₄
  have H₄ := H₃.accR hP₄ (sub1 mT2)
  have G : PPostB s₁ s₄ [(pT, 1024), (sc oSS, 1024), (pT2, 1024)] :=
    (hP₂.trans hP₃ (by decide) (by decide) (by decide)).trans hP₄ (by decide) (fun _ h => h) (by decide)
  have hW₄ := (L.post H₁).keepPoly G R.keepW (by rw [pa_rbx hP₁]; exact hq₁)
  have a₄ : pa s₄ pT2 = pa s₃ pT2 := pa_rbx hP₄ _
  refine WP.seq (WP.mono (subAt_ok C.sub (L.post H₄) R.sub hW₄.1 (by rw [a₄]; exact hq₄.1))
    fun s₅ ⟨hP₅, e₅, hq₅⟩ => ?_)
  rw [hW₄.2, a₄, hq₄.2] at hq₅
  have H₅ := H₄.accR hP₅ (sub1 mW)
  have a₅ : pa s₅ pW = pa s₄ pW := pa_rbx hP₅ _
  refine WP.seq (WP.mono (ipAt_ok C.invNtt (L.post H₅) R.ipW (by rw [a₅]; exact hq₅.1)) fun s₆ ⟨hP₆, e₆, hq₆⟩ => ?_)
  rw [a₅, hq₅.2] at hq₆
  have H₆ := H₅.accR hP₆ (sub2 mW mS)
  have hh₆ := L.keepHint H₆ hH hs.hint
  have a₆ : pa s₆ pW = pa s₄ pW := (pa_rbx hP₆ _).trans a₅
  refine WP.seq (WP.mono (useHintAt_ok C.useHint (L.post H₆) R.g2 R.uh (by rw [a₆]; exact hq₆.1))
    fun s₇ ⟨hP₇, e₇, hq₇⟩ => ?_)
  have hq₇' : natPolyAt s₇.mem (pa s₆ pW1) = _ := hq₇
  rw [hintRow_pa s₆ r, hintAt_row hh₆ hr, a₆, hq₆.2] at hq₇'
  have H₇ := H₆.accR hP₇ (sub1 mW1)
  have a₇ : pa s₇ pW1 = pa s₆ pW1 := pa_rbx hP₇ _
  have hb : ∀ i < n, (coeffAt s₇.mem (pa s₇ pW1) i).toNat ≤ w1Max p := fun i hi => by
    have := congrArg (·[i]'hi) hq₇'
    simp only [natPolyAt, Vector.getElem_ofFn, Vector.getElem_zipWith] at this
    rw [a₇, this, R.max]
    exact useHint_le R.g2 _ _
  refine WP.mono (sbpAt_ok C.simpleBitPack (L.post H₇) R.sbpB R.len R.sbp hb) fun s₈ ⟨hP₈, e₈, hq₈⟩ => ?_
  rw [a₇, hq₇'] at hq₈
  have H₈ := H₇.accR hP₈ (sub1 mB)
  refine ⟨hs.t.step hp hv H₈ tk, L.keepHint H₈ hH hs.hint,
    fun r' hr' c hc => L.keepPoly H₈ (hA r' hr' c hc) (hs.a r' hr' c hc),
    fun i hi => L.keepPoly H₈ (hZ i hi (by have := kl_le p hp; omega)) (hs.z i hi), L.keepPoly H₈ R.keepC' hs.c,
    fun r' hr' => ?_, by rw [e₈, e₇, e₆, e₅, e₄, e₃, e₂, e₁]; exact hs.r15⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hr' with hlt | rfl
  · rw [L.keepBytes H₈ (R.rows r' hlt)]; exact hs.rows r' hlt
  · rw [show pa s₈ (sc (oB + w1Len p * r')) = pa s₇ (sc (oB + w1Len p * r')) from pa_rbx hP₈ _, hq₈]
    rfl

/-! ## The rows, the hash and the comparison -/

theorem bytesAt_rows {m : Mem} {a : Addr} {L : Nat} {f : Nat → List Byte} :
    ∀ k, (∀ r < k, bytesAt m (a + BitVec.ofNat 64 (L * r)) L = f r) → bytesAt m a (k * L) = (List.range k).flatMap f
  | 0, _ => by rw [Nat.zero_mul]; rfl
  | k + 1, h => by
    rw [Nat.succ_mul, Proof.MlKem.bytesAt_add, bytesAt_rows k (fun r hr => h r (by omega)), Nat.mul_comm k L,
      h k (by omega), List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem row_pa (s : State) (L r : Nat) : pa s (sc (oB + L * r)) = pa s (sc oB) + BitVec.ofNat 64 (L * r) := by
  simp only [pa]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The facts about the parameters the hash and the comparison need. -/
def compChk (p : Params) : Bool :=
  hashChk (vB p) (vW p) (.r12, 0) 64 (sc oB) (p.k * w1Len p) (sc oCT) p.ctildeLen &&
    tChk p [(sc 0, 200), (sc 200, 640), (sc oCT, p.ctildeLen)] && inB (vB p) (sc oCT) p.ctildeLen &&
    inB (vB p) (.r13, 0) p.ctildeLen && decide (0 < p.ctildeLen) && decide (p.ctildeLen ≤ p.sigLen)

theorem compChk_all : ∀ p ∈ params, compChk p = true := by decide

/-- `w′₁` of the signature, encoded. -/
abbrev w1Enc (p : Params) (σ : State) (h : List (Vector Bool n)) (A' : Nat → Nat → Poly) (cH : Poly) :
    List Byte :=
  (List.range p.k).flatMap fun r => simpleBitPack (w1Row p (vPk p σ) (vSig p σ) A' cH h r) (w1Max p)

theorem compute_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
    {s : State} (hs : SC p h A' Q 0 cH 0 σ s) :
    WP isa (compute P p) s fun s' => T p σ s' ∧
      s'.gpr .r15 = flag (Q ∧ H (vMu σ ++ w1Enc p σ h A' (ntt cH)) p.ctildeLen = vCt p (vSig p σ)) := by
  have hc := compChk_all p hp
  simp only [compChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩ := hc
  unfold compute
  refine WP.seq (WP.mono (seqR_ok (I := fun i => SC p h A' Q i cH 0 σ) p.ℓ 0
    (fun i _ hi st hst => nttZ_ok C hp hv (by omega) hst) s hs) fun s₁ hs₁ => ?_)
  rw [Nat.zero_add] at hs₁
  refine WP.seq (WP.mono (nttC_ok C hp hv hs₁) fun s₂ hs₂ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun r => SC p h A' Q p.ℓ (ntt cH) r σ) p.k 0
    (fun r _ hr st hst => row_ok C hp hv (by omega) hst) s₂ hs₂) fun s₃ hs₃ => ?_)
  rw [Nat.zero_add] at hs₃
  have L₃ := hs₃.t.lay hp hv
  have hB : bytesAt s₃.mem (pa s₃ (sc oB)) (p.k * w1Len p) = w1Enc p σ h A' (ntt cH) :=
    bytesAt_rows p.k fun r hr => by rw [← row_pa]; exact hs₃.rows r hr
  refine WP.seq (WP.mono (hash2_ok L₃ c1) fun s₄ ⟨hP₄, f₄, hq₄⟩ => ?_)
  rw [hB, hs₃.t.mu] at hq₄
  have t₄ := hs₃.t.step hp hv hP₄ c2
  have L₄ := t₄.lay hp hv
  refine WP.mono (cmpAnd_ok L₄ c5 c3 c4 (P := Q) (by rw [f₄]; exact hs₃.r15)) fun s₅ ⟨hP₅, f₅⟩ => ⟨t₄.step hp hv hP₅
    (tChk_nil p hp), ?_⟩
  rw [f₅, show pa s₄ (sc oCT) = pa s₃ (sc oCT) from pa_rbx hP₄ _, hq₄, t₄.sigSlice (by omega : 0 + p.ctildeLen ≤ p.sigLen), List.drop_zero]
  exact flag_congr (and_congr_right fun _ => Iff.rfl)

end VG.Proof.MlDsa.X86_64.Verify
