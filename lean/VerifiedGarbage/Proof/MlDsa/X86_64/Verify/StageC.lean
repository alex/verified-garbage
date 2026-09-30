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
open VG.Proof.MlDsa.Verify (vHint vZ vCt vRho aSeed zHat dotAcc t1Hat wRow w1Row vT1)

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

end VG.Proof.MlDsa.X86_64.Verify
