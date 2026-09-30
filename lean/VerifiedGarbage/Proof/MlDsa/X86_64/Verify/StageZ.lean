import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.PrimsOk

/-!
# ML-DSA verification on x86-64: the hint and `z`

Untrusted: everything here is checked by Lean. `HintIs` the hint of the
signature, and `r15` whether it is well formed (`hint_ok`); then, if it is,
`z[i]` (polynomial `8 + i`) and `r15` whether each norm so far is small
(`zOne_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt)

/-- The `len` bytes at offset `off` of the signature. -/
theorem T.sigSlice {p : Params} {σ s : State} (h : T p σ s) {off len : Nat} (hl : off + len ≤ p.sigLen) :
    bytesAt s.mem (pa s (.r13, off)) len = ((vSig p σ).drop off).take len := by
  rw [← h.sig, pa, pa, BitVec.add_zero, Proof.MlKem.bytesAt_slice _ _ hl]

theorem T.pkSlice {p : Params} {σ s : State} (h : T p σ s) {off len : Nat} (hl : off + len ≤ p.pkLen) :
    bytesAt s.mem (pa s (.rbp, off)) len = ((vPk p σ).drop off).take len := by
  rw [← h.pk, pa, pa, BitVec.add_zero, Proof.MlKem.bytesAt_slice _ _ hl]

theorem lenZ_eq (p : Params) : VG.Impl.MlDsa.X86_64.Verify.lenZ p = VG.Proof.MlDsa.Verify.lenZ p := rfl

/-! ## The hint -/

/-- After the hint: `r15` whether it is well formed, and the hint. -/
def S1 (p : Params) (σ s : State) : Prop :=
  T p σ s ∧ match vHint p (vSig p σ) with
    | some h => s.gpr .r15 = flag True ∧ HintIs s.mem (pa s (pH 0)) p.k h
    | none => s.gpr .r15 = flag False

/-- The facts about the parameters the hint needs. -/
def hintChk (p : Params) : Bool :=
  huChk (vB p) (vW p) (.r13, oHint p) (p.ω + p.k) (pH 0) (256 * p.k) &&
    tChk p [(pH 0, 256 * p.k * 4)] && decide (HuPar (p.ω + p.k) p.ω (256 * p.k)) &&
    decide (oHint p + (p.ω + p.k) ≤ p.sigLen)

theorem hintChk_all : ∀ p ∈ params, hintChk p = true := by decide

theorem hint_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ s : State} (hv : VPre p σ)
    (h : T p σ s) : WP isa (hint P p) s (S1 p σ) := by
  have hc := hintChk_all p hp
  simp only [hintChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc
  have L := h.lay hp hv
  unfold hint
  refine WP.seq (WP.mono (hintUnpackAt_ok C.hintUnpack L c3 c1) fun s₁ ⟨hP₁, _, hq₁⟩ => ?_)
  have h₁ := h.step hp hv hP₁ c2
  refine WP.mono (mov15_ok s₁) fun s₂ ⟨⟨h15, hm₂⟩, k₂⟩ => ?_
  have hP₂ : PPostB s₁ s₂ [] := postB_of_keep k₂ (by decide) (by rw [hm₂]; exact Frame.refl _ _)
  refine ⟨h₁.step hp hv hP₂ (tChk_nil p hp), ?_⟩
  rw [h.sigSlice c4, show p.ω + p.k - p.ω = p.k by omega] at hq₁
  have e : pa s₂ (pH 0) = pa s (pH 0) := by rw [hP₂.pa (by decide), hP₁.pa (by decide)]
  have hv' : vHint p (vSig p σ) = hintBitUnpack p.ω p.k (((vSig p σ).drop (oHint p)).take (p.ω + p.k)) := rfl
  rw [hv']
  revert hq₁
  generalize hintBitUnpack p.ω p.k (((vSig p σ).drop (oHint p)).take (p.ω + p.k)) = H
  cases H with
  | some hh =>
    intro ⟨hr, hH⟩
    simp only [res] at hr
    refine ⟨by rw [h15, hr]; rfl, ?_⟩
    rw [e, hm₂]; exact hH
  | none =>
    intro hr
    simp only [res] at hr
    show s₂.gpr .r15 = flag False
    rw [h15, hr]; rfl


/-! ## `z` -/

/-- After `z[0], …, z[j - 1]`, with the hint `h`. -/
structure S2 (p : Params) (h : List (Vector Bool n)) (j : Nat) (σ s : State) : Prop where
  t : T p σ s
  hint : HintIs s.mem (pa s (pH 0)) p.k h
  z : ∀ i < j, PolyIs s.mem (pa s (pZ i)) (toRq (vZ p (vSig p σ) i))
  r15 : s.gpr .r15 = flag (∀ i < j, normRq [toRq (vZ p (vSig p σ) i)] < p.γ₁ - p.β)

/-- The facts about the parameters `z[i]` needs. -/
def zChk (p : Params) (i : Nat) : Bool :=
  buChk (vB p) (vW p) (.r13, p.ctildeLen + lenZ p * i) (lenZ p) (pZ i) &&
    decide ((p.γ₁ - 1, p.γ₁) ∈ bitPackParams) && decide (lenZ p = 32 * bitlen (p.γ₁ - 1 + p.γ₁)) &&
    decide (p.ctildeLen + lenZ p * i + lenZ p ≤ p.sigLen) && tChk p [(pZ i, 1024)] &&
    keepB (vB p) [(pZ i, 1024)] (pH 0) (1024 * p.k) &&
    (List.range i).all (fun i' => keepB (vB p) [(pZ i, 1024)] (pZ i') 1024) && nlChk (vB p) (pZ i) &&
    decide (p.γ₁ - p.β < 2 ^ 31)

theorem zChk_all : ∀ p ∈ params, ∀ i < p.ℓ, zChk p i = true := by decide

theorem zOne_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {i : Nat} (hi : i < p.ℓ) {s : State} (hs : S2 p h i σ s) :
    WP isa (zOne P p i) s (S2 p h (i + 1) σ) := by
  have hc := zChk_all p hp i hi
  simp only [zChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩ := hc
  have L := hs.t.lay hp hv
  unfold zOne
  refine WP.seq (WP.mono (bitUnpackAt_ok C.bitUnpack L c2 c3 c1) fun s₁ ⟨hP₁, h15₁, hq₁⟩ => ?_)
  have t₁ := hs.t.step hp hv hP₁ c5
  have L₁ := t₁.lay hp hv
  rw [hs.t.sigSlice c4] at hq₁
  have e₁ : pa s₁ (pZ i) = pa s (pZ i) := hP₁.pa (show Reg.rbx ∈ bases by decide)
  rw [← e₁] at hq₁
  refine WP.seq (WP.mono (normLtAt_ok C.normLt L₁ c9 c8 hq₁.1) fun s₂ ⟨hP₂, h15₂, hr₂⟩ => ?_)
  have t₂ := t₁.step hp hv hP₂ (tChk_nil p hp)
  refine WP.mono (and15_ok s₂) fun s₃ ⟨⟨h15₃, hm₃⟩, k₃⟩ => ?_
  have hP₃ : PPostB s₂ s₃ [] := postB_of_keep k₃ (by decide) (by rw [hm₃]; exact Frame.refl _ _)
  have hP₂₃ : PPostB s₁ s₃ [] := PPostB.trans hP₂ hP₃ (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
  refine ⟨t₂.step hp hv hP₃ (tChk_nil p hp), ?_, fun i' hi' => ?_, ?_⟩
  · exact L₁.keepHint hP₂₃ (keepB_nil c6) (L.keepHint hP₁ c6 hs.hint)
  · rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
    · exact L₁.keepPoly hP₂₃ (keepB_nil (c7 i' hi')) (L.keepPoly hP₁ (c7 i' hi') (hs.z i' hi'))
    · exact L₁.keepPoly hP₂₃ (keepB_nil_of (show Reg.rbx ∈ bases by decide) c8) hq₁
  · rw [h15₃, h15₂, h15₁, hs.r15]
    have hr : res s₂ = 1 ∨ res s₂ = 0 := by
      rw [hr₂]
      by_cases hh : normRq [polyAt s₁.mem (pa s₁ (pZ i))] < p.γ₁ - p.β
      · left; rw [ifp hh]
      · right; rw [ifn hh]
    rw [and_flag hr]
    have hq2 : polyAt s₁.mem (pa s₁ (pZ i)) = toRq (vZ p (vSig p σ) i) := hq₁.2
    refine flag_congr ⟨fun ⟨h1, h2⟩ i' hi' => ?_, fun h1 => ⟨fun i' hi' => h1 i' (by omega), ?_⟩⟩
    · rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
      · exact h1 i' hi'
      · rw [hr₂, hq2] at h2
        by_contra hn; rw [ifn hn] at h2; cases h2
    · rw [hr₂, hq2, ifp (h1 i (by omega))]

end VG.Proof.MlDsa.X86_64.Verify
