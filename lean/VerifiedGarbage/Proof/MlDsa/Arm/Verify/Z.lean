import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Hint

/-!
# ML-DSA verification on 32-bit ARM: `z`

Untrusted: everything here is checked by Lean. Once the hint is well formed:
each `z[i]`, unpacked from the signature to polynomial `8 + i`, and its norm
checked, with `r11` 1 exactly when every `‖z[i]‖∞` so far is less than
`γ₁ - β` (`V2`, `zOne_piece`).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee BuOk bu_okS
  bu_tr nl_ok nl_tr polyIs_keepW keepD)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (and11)
open VG.Spec.MlDsa (Params HintIs PolyIs toRq polyAt normRq Reduced)
open VG.Proof.MlDsa.Verify (vZ)
open VG.Spec.Sha3 (bytesAt)

/-- `‖z[i]‖∞ < γ₁ - β` for every `i < j`. -/
abbrev zOk (p : Params) (σ : State) (j : Nat) : Bool :=
  decide (∀ i < j, normRq [toRq (vZ p (sgOf p σ) i)] < p.γ₁ - p.β)

/-- A hint kept by a part that writes apart from it. -/
theorem hintIs_keepW {L : Lay} {Wb : List Nat} (hL : OkW L Wb) {W : List (Nat × Nat × Nat)} {m m' : Mem}
    (hf : Frame (L.RL W) m m') {i o k : Nat} (h : sepAll L.sizes (i, o, 1024 * k) W = true) (hw : i ∈ Wb)
    (hk : 1024 * k ≤ 2 ^ 64) {hh : List (Vector Bool Spec.MlDsa.n)} (hi : HintIs m (L.A i o) k hh) :
    HintIs m' (L.A i o) k hh :=
  Proof.MlDsa.Verify.hintIs_frame hf hk (keepD hL h hw) hi

/-- After the hint and the first `j` of `z`. -/
structure V2 (p : Params) (STK : Nat) (j : Nat) (σ s : State) : Prop where
  vc : VC p STK σ s
  hint : ∃ h, hintOf p σ = some h ∧ HintIs s.mem ((vlay p STK σ).A 0 (oP 0)) p.k h
  z : ∀ i < j, PolyIs s.mem ((vlay p STK σ).A 0 (oP (8 + i))) (toRq (vZ p (sgOf p σ) i))
  r11 : s.gpr .r11 = flag (zOk p σ j)

theorem V2.keep {p : Params} (hF : VFacts p) {STK j : Nat} {σ s s' : State} (h : V2 p STK j σ s)
    {W : List (Nat × Nat × Nat)} (hk : Kept ((vlay p STK σ).RL W) s s') (hc : vcChk p STK W = true)
    (hh : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 0, 1024 * p.k) W = true)
    (hz : ∀ i < j, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (8 + i), 1024) W = true)
    (h11 : s'.gpr .r11 = s.gpr .r11) : V2 p STK j σ s' := by
  have hL := h.vc.site.ok
  obtain ⟨hh', e, hi⟩ := h.hint
  exact ⟨h.vc.keep hk hc, ⟨hh', e, hintIs_keepW hL hk.frame hh (by decide) (by have := hF.k; omega) hi⟩,
    fun i hi' => polyIs_keepW hL hk.frame (hz i hi') (by decide) rfl (h.z i hi'), by rw [h11]; exact h.r11⟩

theorem flag_and (a b : Bool) : flag a &&& flag b = flag (a && b) := by
  cases a <;> cases b <;> decide

theorem zOk_succ (p : Params) (σ : State) (j : Nat) :
    zOk p σ (j + 1) = (zOk p σ j && decide (normRq [toRq (vZ p (sgOf p σ) j)] < p.γ₁ - p.β)) := by
  simp only [zOk]
  rw [← Bool.decide_and]
  refine decide_eq_decide.mpr (Iff.intro (fun h => ⟨fun i hi => h i (by omega), h j (by omega)⟩) fun h i hi => ?_)
  rcases (by omega : i < j ∨ i = j) with hi | rfl
  exacts [h.1 i hi, h.2]

/-! ## One `z[i]` -/

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

omit hP hS in
theorem bu_m {σ : State} {j : Nat} (hj : j < p.ℓ) :
    BuOk (vlay p STK σ) vWb (.r6, p.ctildeLen + lenZ p * j) (lenZ p) (p.γ₁ - 1) p.γ₁ (pZ j) := by
  have hl := hF.l
  obtain ⟨hb, hlz, hg⟩ := hF.bu
  refine ⟨⟨rfl, ?_⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ vWb by decide, ?_, hb, hlz, ?_⟩
  · rcases hF.lz with e | e <;> vsep hF [hF.sig, hF.hint, e]
  · rcases hF.lz with e | e <;> vsep hF [hF.sig, hF.hint, e]
  · rcases hF.lz with e | e <;> rw [e] <;> omega

/-- After `z[j]` is unpacked. -/
abbrev Z1 (p : Params) (STK j : Nat) (σ s : State) : Prop :=
  V2 p STK j σ s ∧ PolyIs s.mem ((vlay p STK σ).A 0 (oP (8 + j))) (toRq (vZ p (sgOf p σ) j))

theorem bu_piece {j : Nat} (hj : j < p.ℓ) :
    VPiece p STK (V2 p STK j) (Z1 p STK j)
      (bitUnpackAt P (.r6, p.ctildeLen + lenZ p * j) (lenZ p) (p.γ₁ - 1) p.γ₁ (pZ j)) := by
  have hl := hF.l
  refine ⟨fun σ s _ h => ?_, ?_⟩
  · unfold bitUnpackAt
    refine bu_okS hP.bitUnpack h.vc.site (by omega) (bu_m hF hj) fun s' k' hz => ⟨h.keep hF k' ?_ ?_ ?_
      (k'.cs .r11 (by decide) (by decide)), ?_⟩
    · rcases hF.lz with e | e <;> vsep hF [vcChk, hF.sig, hF.hint, e]
    · vsep hF
    · intro i hi; vsep hF
    · have e : bytesAt s.mem (lpa (vlay p STK σ) (.r6, p.ctildeLen + lenZ p * j)) (lenZ p) =
          ((sgOf p σ).drop (p.ctildeLen + lenZ p * j)).take (lenZ p) :=
        sig_slice h.vc (by rw [hF.sig, hF.hint]; rcases hF.lz with e | e <;> rw [e] <;> omega)
      rw [e] at hz
      exact hz
  · unfold bitUnpackAt
    exact rel_of (RelCT.exists_ fun σ => bu_tr hP.bitUnpack (by omega) (bu_m hF hj) fun x y h => h)
      fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩

/-- After the norm of `z[j]`. -/
abbrev Z2 (p : Params) (STK j : Nat) (σ s : State) : Prop :=
  Z1 p STK j σ s ∧ s.gpr .r0 = flag (decide (normRq [toRq (vZ p (sgOf p σ) j)] < p.γ₁ - p.β))

theorem nl_piece {j : Nat} (hj : j < p.ℓ) :
    VPiece p STK (Z1 p STK j) (Z2 p STK j) (normLtAt P (pZ j) (p.γ₁ - p.β)) := by
  have hl := hF.l
  refine ⟨fun σ s _ h => ?_, ?_⟩
  · unfold normLtAt
    have hr0 : Reduced s.mem (lpa (vlay p STK σ) (pZ j)) := h.2.1
    have pf : PtrIn (vlay p STK σ) (pZ j) 1024 := ⟨rfl, by vsep hF⟩
    have hb : p.γ₁ - p.β < 2 ^ 32 := hF.nb.1
    refine nl_ok hP.normLt h.1.vc.site (by omega) (bd := p.γ₁ - p.β) pf hb hr0 fun s' k' hr => ⟨⟨h.1.keep hF k'
      (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF) (k'.cs .r11 (by decide) (by decide)),
      polyIs_keepW h.1.vc.site.ok k'.frame (by vsep hF) (by decide) rfl h.2⟩, ?_⟩
    rw [hr, show polyAt s.mem (lpa (vlay p STK σ) (pZ j)) = _ from h.2.2, flag]
    simp only [decide_eq_true_eq]
  · unfold normLtAt
    refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      Reduced x.mem (lpa (vlay p STK σ) (pZ j)) ∧ Reduced y.mem (lpa (vlay p STK σ) (pZ j)))
      (RelCT.exists_ fun σ => nl_tr hP.normLt (by omega) (bd := p.γ₁ - p.β)
        (⟨rfl, by vsep hF⟩ : PtrIn (vlay p STK σ) (pZ j) 1024) fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub h₁ h₂ => ?_
    have r₂ : Reduced _ (lpa (vlay p STK _) (pZ j)) := h₂.2.1
    rw [← vlay_pub pub] at r₂
    exact ⟨σ₁, vc_twoL pub h₁.1.vc h₂.1.vc, h₁.2.1, r₂⟩

omit hP hF hS in
theorem and11_piece {j : Nat} : VPiece p STK (Z2 p STK j) (V2 p STK (j + 1)) (.block and11) := by
  refine ⟨fun σ s _ h => ?_, vrel7 (fun _ _ h => h.1.1.vc) (by taint_decide)⟩
  apply WP.of_runBlock
  simp only [and11, runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨h.1.1.vc.r11 _, h.1.1.hint, fun i hi => ?_, ?_⟩
  · rcases (by omega : i < j ∨ i = j) with hi | rfl
    exacts [h.1.1.z i hi, h.1.2]
  · rw [gpr_setReg_self, h.1.1.r11, h.2, flag_and, zOk_succ]

theorem zOne_piece {j : Nat} (hj : j < p.ℓ) : VPiece p STK (V2 p STK j) (V2 p STK (j + 1)) (zOne P p j) :=
  (bu_piece hP hF hS hj).seq ((nl_piece hP hF hS hj).seq and11_piece)

end

end VG.Proof.MlDsa.Arm.Verify
