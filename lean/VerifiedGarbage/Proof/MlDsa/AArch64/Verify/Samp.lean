import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Z
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp

/-!
# ML-DSA verification on AArch64: the samplers

`ρ` to the seed (`copyRho_vpiece`); each entry `Â[r, s]` sampled from `ρ ‖ s ‖
r` (`expA_vpiece`), and `c` (`ball_vpiece`), each reduced, and `x24` 1 only if
every sampler succeeded, with their outputs (`VA`, `VB`). Each sampler's
output is masked with its result, without a branch; the seeds are functions of
the public key and the signature, the same in two runs.
-/

namespace VG.Proof.MlDsa.AArch64.Verify

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq polyAt coeffAt Reduced PolyIs Bounds minBounds rejNTTPoly sampleInBall
  Outcome)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Impl.MlKem.AArch64 (copy32)
open VG.Proof.MlKem.AArch64 (Keep)

/-- The seed of entry `e = rℓ + s` of `Â`. -/
abbrev seedOf (p : Params) (σ : State) (e : Nat) : List Byte :=
  Proof.MlDsa.Verify.aSeed (vPk p σ) (e / p.ℓ) (e % p.ℓ)
/-- `c̃`. -/
abbrev ctOf (p : Params) (σ : State) : List Byte := Proof.MlDsa.Verify.vCt p (vSig p σ)

/-- After the first `e` entries of `Â`. -/
structure VA (p : Params) (σ : State) (e : Nat) (s : State) : Prop where
  vz : VZ p σ p.ℓ s
  nok : normOk p σ p.ℓ
  rho : bytesAt s.mem (pa s (sc oSA)) 32 = (vPk p σ).take 32
  red : ∀ e' < e, Reduced s.mem (pa s (aP e'))
  ok : ∃ q : Bool, s.gpr .x24 = flag (q = true) ∧
    (q = true → ∀ e' < e, ∃ b : Bounds, rejNTTPoly b.rejNTT (seedOf p σ e') = some (polyAt s.mem (pa s (aP e')))) ∧
    (q = false → ∃ e' < e, rejNTTPoly minBounds.rejNTT (seedOf p σ e') = none)

/-- A piece that writes `ws` keeps `VA`. -/
structure VAChk (p : Params) (e : Nat) (ws : List (Ptr × Nat)) : Prop where
  vz : VZChk p p.ℓ ws
  rho : keepB (vR p) (vW p) ws (sc oSA) 32 = true
  a : ∀ e' < e, keepB (vR p) (vW p) ws (aP e') 1024 = true

/-- Proves a `VAChk`. -/
syntax "vachk " term:max : tactic
macro_rules
  | `(tactic| vachk $hF) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr; have := ($hF).small
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> intros <;> (try unfold VG.Proof.MlDsa.AArch64.Verify.vcChk) <;> vlay))

theorem VA.keep {p : Params} (hF : VFacts p) {S : Nat} {σ : State} (hp : vPre p S σ) {e : Nat} {s s' : State}
    (h : VA p σ e s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : VAChk p e ws)
    (h24 : s'.gpr .x24 = s.gpr .x24) : VA p σ e s' := by
  have L := h.vz.vc.lay hF hp
  obtain ⟨q, hq, h1, h0⟩ := h.ok
  refine ⟨h.vz.keep hF hp hP hc.vz, h.nok, by rw [L.keepBytes hP hc.rho]; exact h.rho,
    fun e' he' => L.keepRed hP (hc.a e' he') (h.red e' he'), q, by rw [h24]; exact hq, fun hq' e' he' => ?_, h0⟩
  obtain ⟨b, hb⟩ := h1 hq' e' he'
  exact ⟨b, by rw [hb, L.keepPolyAt hP (hc.a e' he')]⟩

/-! ## `ρ` -/

theorem copyRho_vpiece {p : Params} (hF : VFacts p) {S : Nat} :
    VPiece p S (fun σ s => Z0 p p.ℓ σ s ∧ normOk p σ p.ℓ) (VA p · 0) (.block (copy32 .x25 0 .x28 oSA)) := by
  have hc : copyPChk (vR p) (vW p) (sc oSA) (.x25, 0) = true := by
    have := hF.k; have := hF.l; have := hF.scr; have := hF.pk; unfold copyPChk; vlay
  refine ⟨fun σ s hp h => ?_, taintRel [.x25, .x28] (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ?_)
    (by taint_decide)⟩
  · have L := h.1.1.vc.lay hF hp
    refine WP.mono (copyP_ok L hc) fun s' ⟨hP', k', hb⟩ => ?_
    refine ⟨h.1.1.keep hF hp hP' (by vzchk hF), h.2, ?_, fun _ h => absurd h (Nat.not_lt_zero _), true, ?_,
      fun _ _ h => absurd h (Nat.not_lt_zero _), fun h => absurd h (by decide)⟩
    · rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide), hb, h.1.1.vc.pkSlice (by rw [hF.pk]; omega), List.drop_zero]
    · rw [k'.get .x24, h.1.2]; exact flag_congr (iff_of_true h.2 rfl)
  · have T := vc_two hF p₁ p₂ pub h₁.1.1.vc h₂.1.1.vc
    refine ⟨T.same.2, fun r hr => T.same.1 r ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide

/-! ## An entry of `Â` -/

/-- The seed of `RejNTTPoly` set. -/
abbrev VA1 (p : Params) (e : Nat) (σ s : State) : Prop :=
  VA p σ e s ∧ bytesAt s.mem (pa s (sc oSA)) 34 = seedOf p σ e

/-- After `RejNTTPoly`. -/
abbrev VA2 (p : Params) (e : Nat) (σ s : State) : Prop :=
  VA p σ e s ∧ ((s.gpr .x0).setWidth 32 = 1 → Reduced s.mem (pa s (aP e))) ∧
    Outcome (fun b => rejNTTPoly b.rejNTT (seedOf p σ e)) ((s.gpr .x0).setWidth 32) (polyAt s.mem (pa s (aP e)))

theorem integerToBytes_one (x : Nat) : Spec.MlDsa.integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [Spec.MlDsa.integerToBytes]

theorem vsetTwo_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {o a b : Nat}
    (ho : o + 1 < 4096) (h1 : inB wbs (sc o) 1 = true) (h2 : inB wbs (sc (o + 1)) 1 = true) :
    WP isa (.block (setB (sc o) a ++ setB (sc (o + 1)) b)) s fun s' =>
      PPostB S s s' [(sc o, 1), (sc (o + 1), 1)] ∧ Keep [.x9] s s' ∧
      bytesAt s'.mem (pa s (sc o)) 2 = [BitVec.ofNat 8 a, BitVec.ofNat 8 b] := by
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok L (p := sc o) (v := a) (by simp only; omega) h1 (show Reg.x28 ∈ keptRegs by decide))
    fun s₁ ⟨hP₁, k₁, m₁⟩ => WP.mono (setB_ok (L.post hP₁) (p := sc (o + 1)) (v := b) ho h2
      (show Reg.x28 ∈ keptRegs by decide))
      fun s₂ ⟨hP₂, k₂, m₂⟩ => ⟨PPostB.app hP₁ hP₂ (sc_bases _ (by simp)), (k₁.trans k₂).mono (by simp), ?_⟩
  have e : pa s₁ (sc (o + 1)) = pa s (sc o) + BitVec.ofNat 64 1 := by
    rw [hP₁.pa (show Reg.x28 ∈ keptRegs by decide), pa, pa, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [m₂, m₁, e]
  exact bytesAt_two _ _ _ _

/-- The AND of a sampler's result and the mask of its output, from the registers `x28`. -/
theorem vtail_taint : ∀ j < 80, (taint.check (AArch64.Taint.ofRegs [.x28]) (.seq (.block and24) (mask (sc (oP j))))
    (VG.Taint.hintOf taint (AArch64.Taint.ofRegs [.x28]) (.seq (.block and24) (mask (sc 0))))).isSome = true := by
  decide +kernel

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) {e : Nat} (he : e < p.k * p.ℓ)
include hP hF he

omit hP in
theorem seed_vpiece : VPiece p S (VA p · e) (VA1 p e)
    (.block (setB (sc (oSA + 32)) (e % p.ℓ) ++ setB (sc (oSA + 33)) (e / p.ℓ))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  refine ⟨fun σ s hp h => ?_, taintRel [.x28] (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
    (vc_two hF p₁ p₂ pub h₁.vz.vc h₂.vz.vc).x28) (setIJ_taint _ (by omega) _ (by omega))⟩
  have L := h.vz.vc.lay hF hp
  refine WP.mono (vsetTwo_ok L (o := oSA + 32) (a := e % p.ℓ) (b := e / p.ℓ) (by decide) (by vlay) (by vlay))
    fun s' ⟨hP', k', hb⟩ => ⟨h.keep hF hp hP' (by vachk hF) (k'.get .x24), ?_⟩
  rw [bytes34, L.keepBytes hP' (by vlay), h.rho, sc_add, sc_pa hP', hb, seedOf, Proof.MlDsa.Verify.aSeed,
    integerToBytes_one, integerToBytes_one, List.append_assoc]
  rfl

omit hP in
theorem rej_chk : rejNttChk (vR p) (vW p) (sc oSA) (aP e) (sc oSS) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr
  unfold rejNttChk; vlay

theorem rej_vpiece : VPiece p S (VA1 p e) (VA2 p e) (rejNttAt P (sc oSS) (sc oSA) (aP e)) := by
  have hc := rej_chk hF he
  refine ⟨fun σ s hp h => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧
    bytesAt x.mem (pa x (sc oSA)) 34 = bytesAt y.mem (pa y (sc oSA)) 34)
    (rejNttAt_tr hP.rejNtt (vOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨vc_two hF p₁ p₂ pub h₁.1.vz.vc h₂.1.vz.vc, by
      rw [h₁.2, h₂.2, seedOf, seedOf, (vPub_eq pub).2.1]⟩⟩
  have L := h.1.vz.vc.lay hF hp
  refine WP.mono (rejNttAt_ok hP.s64 hP.rejNtt L hc) fun s' ⟨hP', x', hred, hout⟩ => ?_
  rw [h.2] at hout
  have e' : pa s' (aP e) = pa s (aP e) := sc_pa hP' _
  refine ⟨h.1.keep hF hp hP' (by vachk hF) x', fun h1 => by rw [e']; exact hred h1, by rw [e']; exact hout⟩

omit hP in
theorem tail_vpiece : VPiece p S (VA2 p e) (VA p · (e + 1)) (.seq (.block and24) (mask (aP e))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr
  refine ⟨fun σ s hp h => ?_, taintRel [.x28] (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
    (vc_two hF p₁ p₂ pub h₁.1.vz.vc h₂.1.vz.vc).x28) (vtail_taint e (by omega))⟩
  have L := h.1.vz.vc.lay hF hp
  obtain ⟨hv, hred, hout⟩ := h
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  refine WP.mono (tail_ok L (a := aP e) (by vlay) (by vlay) hr01) fun s' ⟨hP', x', hco⟩ => ?_
  have hvz := hv.vz.keep hF hp hP' (by vzchk hF)
  have e' : pa s' (aP e) = pa s (aP e) := sc_pa hP' _
  obtain ⟨q, hq, h1, h0⟩ := hv.ok
  rw [hq] at x'
  have hA : ∀ e' < e, polyAt s'.mem (pa s' (aP e')) = polyAt s.mem (pa s (aP e')) := fun e' he' =>
    L.keepPolyAt hP' (by vlay)
  refine ⟨hvz, hv.nok, by rw [L.keepBytes hP' (by vlay)]; exact hv.rho, fun e'' he'' => ?_, q && ((s.gpr .x0).setWidth 32 == 1), ?_, fun hq' e'' he'' => ?_,
    fun hq' => ?_⟩
  · rcases (by omega : e'' < e ∨ e'' = e) with he'' | rfl
    · exact L.keepRed hP' (by vlay) (hv.red e'' he'')
    · rw [e']
      by_cases h1 : (s.gpr .x0).setWidth 32 = 1
      · exact (Proof.MlDsa.KeyGen.masked_one h1 hco).2 (hred h1)
      · exact (Proof.MlDsa.KeyGen.masked_zero h1 hco).1
  · rw [x', and_flag _ (Q := (s.gpr .x0).setWidth 32 = 1) (by rcases hr01 with h | h <;> rw [h] <;> decide)]
    exact flag_congr (by simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    rcases (by omega : e'' < e ∨ e'' = e) with he'' | rfl
    · obtain ⟨b, hb⟩ := h1 hq'.1 e'' he''
      exact ⟨b, by rw [hb, hA e'' he'']⟩
    · rcases hout with ⟨_, b, hb⟩ | ⟨h0', _⟩
      · exact ⟨b, by rw [e', (Proof.MlDsa.KeyGen.masked_one hq'.2 hco).1]; exact hb⟩
      · rw [hq'.2] at h0'; exact absurd h0' (by decide)
  · cases hqq : q
    · obtain ⟨e'', he'', hn⟩ := h0 hqq
      exact ⟨e'', by omega, hn⟩
    · rw [hqq] at hq'
      simp only [Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hq'
      rcases hout with ⟨h1', _⟩ | ⟨_, hn⟩
      · exact absurd h1' hq'
      · exact ⟨e, by omega, hn⟩

theorem expA_vpiece : VPiece p S (VA p · e) (VA p · (e + 1)) (expA P p e) := by
  unfold expA sampled
  exact (seed_vpiece hF he).seq ((rej_vpiece hP hF he).seq (tail_vpiece hF he))

end

/-! ## `c` -/

/-- After the samplers. -/
structure VB (p : Params) (σ : State) (s : State) : Prop where
  vz : VZ p σ p.ℓ s
  nok : normOk p σ p.ℓ
  red : ∀ e < p.k * p.ℓ, Reduced s.mem (pa s (aP e))
  redC : Reduced s.mem (pa s (cP p))
  ok : ∃ q : Bool, s.gpr .x24 = flag (q = true) ∧
    (q = true → (∀ e < p.k * p.ℓ, ∃ b : Bounds, rejNTTPoly b.rejNTT (seedOf p σ e) = some (polyAt s.mem (pa s (aP e)))) ∧
      ∃ b : Bounds, (sampleInBall p.τ b.ball (ctOf p σ)).map toRq = some (polyAt s.mem (pa s (cP p)))) ∧
    (q = false → (∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (seedOf p σ e) = none) ∨
      (sampleInBall p.τ minBounds.ball (ctOf p σ)).map toRq = none)

/-- After `SampleInBall`. -/
abbrev VB1 (p : Params) (σ s : State) : Prop :=
  VA p σ (p.k * p.ℓ) s ∧ ((s.gpr .x0).setWidth 32 = 1 → Reduced s.mem (pa s (cP p))) ∧
    Outcome (fun b => (sampleInBall p.τ b.ball (ctOf p σ)).map toRq) ((s.gpr .x0).setWidth 32)
      (polyAt s.mem (pa s (cP p)))

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
include hP hF

omit hP in
theorem ball_chk : ballChk (vR p) (vW p) (.x27, 0) p.ctildeLen (cP p) (sc oSS) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr; have := hF.ct; have := hF.sig
  unfold ballChk; vlay

omit hP in
theorem ctOf_eq {σ s : State} (h : VC p σ s) : bytesAt s.mem (pa s (.x27, 0)) p.ctildeLen = ctOf p σ := by
  have := hF.sig
  rw [h.slice (by omega), List.drop_zero]; rfl

theorem ballCall_vpiece : VPiece p S (VA p · (p.k * p.ℓ)) (VB1 p)
    (ballAt P (sc oSS) (.x27, 0) p.ctildeLen p.τ (cP p)) := by
  have hc := ball_chk hF
  refine ⟨fun σ s hp h => ?_, vrel_of (Q := fun x y => VTwo p S x y ∧
    bytesAt x.mem (pa x (.x27, 0)) p.ctildeLen = bytesAt y.mem (pa y (.x27, 0)) p.ctildeLen)
    (ballAt_tr hP.ball (vOk p) hc hF.ct.1 fun x y h => ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨vc_two hF p₁ p₂ pub h₁.vz.vc h₂.vz.vc, by
      rw [ctOf_eq hF h₁.vz.vc, ctOf_eq hF h₂.vz.vc, ctOf, ctOf, (vPub_eq pub).2.2.2.1]⟩⟩
  have L := h.vz.vc.lay hF hp
  refine WP.mono (ballAt_ok hP.s64 hP.ball L hc hF.ct.1) fun s' ⟨hP', x', hred, hout⟩ => ?_
  rw [ctOf_eq hF h.vz.vc] at hout
  have e' : pa s' (cP p) = pa s (cP p) := sc_pa hP' _
  refine ⟨h.keep hF hp hP' (by vachk hF) x', fun h1 => by rw [e']; exact hred h1, by rw [e']; exact hout⟩

omit hP in
theorem ballTail_vpiece : VPiece p S (VB1 p) (VB p) (.seq (.block and24) (mask (cP p))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := hF.scr
  refine ⟨fun σ s hp h => ?_, taintRel [.x28] (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
    (vc_two hF p₁ p₂ pub h₁.1.vz.vc h₂.1.vz.vc).x28) (vtail_taint _ (by omega))⟩
  have L := h.1.vz.vc.lay hF hp
  obtain ⟨hv, hred, hout⟩ := h
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  refine WP.mono (tail_ok L (a := cP p) (by vlay) (by vlay) hr01) fun s' ⟨hP', x', hco⟩ => ?_
  have hvz := hv.vz.keep hF hp hP' (by vzchk hF)
  have e' : pa s' (cP p) = pa s (cP p) := sc_pa hP' _
  obtain ⟨q, hq, h1, h0⟩ := hv.ok
  rw [hq] at x'
  refine ⟨hvz, hv.nok, fun e he => L.keepRed hP' (by vlay) (hv.red e he), ?_, q && ((s.gpr .x0).setWidth 32 == 1), ?_, fun hq' => ⟨fun e he => ?_, ?_⟩,
    fun hq' => ?_⟩
  · rw [e']
    by_cases h1 : (s.gpr .x0).setWidth 32 = 1
    · exact (Proof.MlDsa.KeyGen.masked_one h1 hco).2 (hred h1)
    · exact (Proof.MlDsa.KeyGen.masked_zero h1 hco).1
  · rw [x', and_flag _ (Q := (s.gpr .x0).setWidth 32 = 1) (by rcases hr01 with h | h <;> rw [h] <;> decide)]
    exact flag_congr (by simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    obtain ⟨b, hb⟩ := h1 hq'.1 e he
    exact ⟨b, by rw [hb, L.keepPolyAt hP' (by vlay)]⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    rcases hout with ⟨_, b, hb⟩ | ⟨h0', _⟩
    · exact ⟨b, by rw [e', (Proof.MlDsa.KeyGen.masked_one hq'.2 hco).1]; exact hb⟩
    · rw [hq'.2] at h0'; exact absurd h0' (by decide)
  · cases hqq : q
    · exact .inl (h0 hqq)
    · rw [hqq] at hq'
      simp only [Bool.true_and, beq_eq_false_iff_ne, ne_eq] at hq'
      rcases hout with ⟨h1'', _⟩ | ⟨_, hn⟩
      · exact absurd h1'' hq'
      · exact .inr hn

end

/-! ## The samplers -/


end VG.Proof.MlDsa.AArch64.Verify
