import VerifiedGarbage.Proof.MlDsa.Arm.Verify.SampA

/-!
# ML-DSA verification on 32-bit ARM: `c`, and the samplers

`c = SampleInBall(c̃)`, masked by its result (`ball_piece`); and the samplers
from the checks of the signature (`samples_piece`): after them (`VS4`), `Â`
and `c` are reduced, and `r11` is 1 if every sampler succeeded, with them
those of the standard for some bounds, and 0 if one fails within the least
bounds.
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee BallOk ball_okS
  ball_tr polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD andMask_ok masked_poly taint7)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (and11 mask setB seqR sampled)
open VG.Impl.MlKem.Arm (copy)
open VG.Spec.MlDsa (Params HintIs PolyIs toRq polyAt normRq Reduced rejNTTPoly minBounds Outcome sampleInBall)
open VG.Proof.MlDsa.Verify (vZ vRho aSeed vCt)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers. -/
structure VS4 (p : Params) (STK : Nat) (σ s : State) : Prop where
  vb : VB p STK σ s
  red : ∀ r < p.k, ∀ s' < p.ℓ, Reduced s.mem (aA p STK σ r s')
  redC : Reduced s.mem ((vlay p STK σ).A 0 (oP 15))
  ok : ∃ q : Bool, s.gpr .r11 = flag q ∧
    (q = true → (∀ r < p.k, ∀ s' < p.ℓ,
      ∃ b : Nat, rejNTTPoly b (aSeed (pkOf p σ) r s') = some (polyAt s.mem (aA p STK σ r s'))) ∧
      ∃ b : Nat, (sampleInBall p.τ b (vCt p (sgOf p σ))).map toRq = some (polyAt s.mem ((vlay p STK σ).A 0 (oP 15)))) ∧
    (q = false → (∃ r < p.k, ∃ s' < p.ℓ, rejNTTPoly minBounds.rejNTT (aSeed (pkOf p σ) r s') = none) ∨
      sampleInBall p.τ minBounds.ball (vCt p (sgOf p σ)) = none)

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

omit hP hS in
theorem ball_m {σ : State} :
    BallOk (vlay p STK σ) vWb (.r6, 0) p.ctildeLen p.τ pC (sc oSS) := by
  have hk := hF.k
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ vWb by decide,
    show ix Reg.r7 ∈ vWb by decide, by vsep hF, by vsep hF, by vsep hF, hF.ball.1,
    ⟨by rcases hF.ct with e | e | e <;> omega, by rcases hF.ct with e | e | e <;> omega, hF.ball.2⟩⟩

theorem ball_ok {σ s : State} (h : VS p STK p.k 0 σ s) :
    WP isa (sampled (ballAt P (.r6, 0) p.ctildeLen p.τ pC) pC) s (VS4 p STK σ) := by
  have hk := hF.k; have hl := hF.l
  have hs := h.vb.vc.site
  have hL := hs.ok
  unfold sampled ballAt
  refine WP.seq (ball_okS hP.ball hs (by omega) (ball_m hF) fun s₃ k₃ hred hout => ?_)
  have eb : bytesAt s.mem (lpa (vlay p STK σ) (.r6, 0)) p.ctildeLen = vCt p (sgOf p σ) := by
    have := sig_slice h.vb.vc (o := 0) (l := p.ctildeLen) (by have := hF.sig; have := hF.hint; omega)
    rw [List.drop_zero] at this
    exact this
  rw [eb] at hout
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  have kv₃ := h.vb.keep hF k₃ (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF)
  have kA3 : ∀ r < p.k, ∀ s' < p.ℓ, polyAt s₃.mem (aA p STK σ r s') = polyAt s.mem (aA p STK σ r s') ∧
      (Reduced s.mem (aA p STK σ r s') → Reduced s₃.mem (aA p STK σ r s')) := fun r hr s' hs' =>
    ⟨polyAt_keepW hL k₃.frame (by vsep hF) (by decide) rfl, reduced_keepW hL k₃.frame (by vsep hF) (by decide) rfl⟩
  have h11₃ : s₃.gpr .r11 = s.gpr .r11 := k₃.cs .r11 (by decide) (by decide)
  refine WP.mono (andMask_ok kv₃.vc.site (a := pC) ⟨rfl, by vsep hF⟩ (show ix Reg.r7 ∈ vWb by decide) hr01)
    fun s₄ ⟨k₄, r₄, co⟩ => ?_
  obtain ⟨pi, p1, _⟩ := masked_poly hred co
  have kv₄ := (kv₃.r11 (s₃.gpr .r11 &&& s₃.gpr .r0)).keep hF k₄ (by vsep hF [vcChk]) (by vsep hF)
    (fun i hi => by vsep hF)
  have kA4 : ∀ r < p.k, ∀ s' < p.ℓ, polyAt s₄.mem (aA p STK σ r s') = polyAt s₃.mem (aA p STK σ r s') ∧
      (Reduced s₃.mem (aA p STK σ r s') → Reduced s₄.mem (aA p STK σ r s')) := fun r hr s' hs' =>
    ⟨polyAt_keepW hL k₄.frame (by vsep hF) (by decide) rfl, reduced_keepW hL k₄.frame (by vsep hF) (by decide) rfl⟩
  have dn : ∀ r s', s' < p.ℓ → (Dn p.k 0 r s' ↔ r < p.k) := fun r s' _ => by simp only [Dn]; omega
  obtain ⟨q, hq, hok, hbad⟩ := h.ok
  refine ⟨kv₄, fun r hr s' hs' => (kA4 r hr s' hs').2 ((kA3 r hr s' hs').2 (h.red r s' hs' ((dn r s' hs').mpr hr))),
    pi.1, ⟨q && decide (s₃.gpr .r0 = 1), ?_, fun hq' => ⟨fun r hr s' hs' => ?_, ?_⟩, fun hq' => ?_⟩⟩
  · rw [r₄, h11₃, hq, flag_and01 q hr01]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
    obtain ⟨b, hb⟩ := hok hq'.1 r s' hs' ((dn r s' hs').mpr hr)
    exact ⟨b, by rw [(kA4 r hr s' hs').1, (kA3 r hr s' hs').1]; exact hb⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
    show ∃ b, _ = some (polyAt s₄.mem (lpa (vlay p STK σ) pC))
    rw [p1 hq'.2]
    rcases hout with ⟨_, b, hb⟩ | ⟨h0, _⟩
    · exact ⟨b.ball, hb⟩
    · rw [h0] at hq'; exact absurd hq'.2 (by decide)
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hq'
    rcases hq' with hq' | hq'
    · obtain ⟨r, s', hs', hd, hn⟩ := hbad hq'
      exact .inl ⟨r, (dn r s' hs').mp hd, s', hs', hn⟩
    · rcases hout with ⟨h1, _⟩ | ⟨_, hn⟩
      · exact absurd h1 hq'
      · exact .inr (Option.map_eq_none_iff.mp hn)

omit hP hF hS in
theorem ballTail_taint : (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc (oP 15))))
    (VG.Taint.hintOf VG.Arm.taint (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc 0))))).isSome = true :=
  vAndMask_taint 15 (by decide)

theorem ball_piece : VPiece p STK (VS p STK p.k 0) (VS4 p STK) (sampled (ballAt P (.r6, 0) p.ctildeLen p.τ pC) pC) := by
  have hk := hF.k
  refine ⟨fun _ _ _ h => ball_ok hP hF hS h, ?_⟩
  unfold sampled ballAt
  refine RelCT.seq (R := VTwo p STK) ?_ (vtaint7 ballTail_taint)
  refine RelCT.mono (M := isa) (P := fun (x y : State) => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
    bytesAt x.mem (lpa (vlay p STK σ) (.r6, 0)) p.ctildeLen = bytesAt y.mem (lpa (vlay p STK σ) (.r6, 0)) p.ctildeLen)
    (RelCT.exists_ fun σ => ?_) (fun _ _ ⟨σ₁, _, _, _, pub, h₁, h₂⟩ => ?_) fun _ _ h => h
  · have ok := fun x (hs : Site (vlay p STK σ) vWb STK x) => ball_okS hP.ball hs (by omega)
      (name := "vg_mldsa_sample_in_ball") (ball_m hF (σ := σ)) (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
    exact (VG.Proof.MlDsa.Arm.KeyGen.RelCT.two (fun _ _ h => h.1)
      (ball_tr hP.ball (by omega) (ball_m hF) fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)
      fun x hs => ok x hs).mono (fun _ _ h => h) fun x y h => ⟨σ, h⟩
  · refine ⟨σ₁, vc_twoL pub h₁.vb.vc h₂.vb.vc, ?_⟩
    show bytesAt _ ((vlay p STK σ₁).A 4 0) _ = bytesAt _ ((vlay p STK σ₁).A 4 0) _
    rw [sig_slice h₁.vb.vc (by have := hF.sig; have := hF.hint; omega), pub.2.2.2.2.2.2.2, vlay_pub pub,
      sig_slice h₂.vb.vc (by have := hF.sig; have := hF.hint; omega)]

/-! ## The samplers -/

omit hP hS in
theorem rho_piece :
    VPiece p STK (fun σ s => V2 p STK p.ℓ σ s ∧ flag (zOk p σ p.ℓ) ≠ 0) (VS p STK 0 0) (copy .r4 0 .r7 oSB 32) := by
  refine ⟨fun σ s _ ⟨h, hn⟩ => ?_, rel_of (vtaint4 (by taint_decide)) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
    ⟨σ₁, vc_twoL pub h₁.1.vc h₂.1.vc⟩⟩
  have hz : zOk p σ p.ℓ = true := by
    cases e : zOk p σ p.ℓ
    · rw [e] at hn; exact absurd rfl hn
    · rfl
  exact rho_ok hF ⟨h.vc, h.hint, h.z, hz⟩ (by rw [h.r11, hz]; rfl)

theorem samples_piece :
    VPiece p STK (fun σ s => V2 p STK p.ℓ σ s ∧ flag (zOk p σ p.ℓ) ≠ 0) (VS4 p STK) (samples P p) :=
  (rho_piece hF).seq ((rows_piece hP hF hS).seq (ball_piece hP hF hS))

end

end VG.Proof.MlDsa.Arm.Verify
