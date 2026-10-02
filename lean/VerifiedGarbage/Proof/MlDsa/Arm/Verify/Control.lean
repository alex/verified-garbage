import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inv
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Call
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# ML-DSA verification on 32-bit ARM: two runs, and the branches

Two runs whose entry states agree on the public data have the same layout
(`vc_twoL`), so that the taint analysis from its pointers checks the parts
without calls (`vtaint7`). A branch on `r11` (`ifOk`) takes the same way in
two runs where `r11` is a function of the public data (`ifOk_piece`).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv taint7 taint4)
open VG.Impl.MlDsa.Arm.Verify
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-! ## Two runs -/

theorem vc_twoL {p : Params} {STK : Nat} {σ₁ σ₂ x y : State} (pub : vPub p σ₁ σ₂) (h₁ : VC p STK σ₁ x)
    (h₂ : VC p STK σ₂ y) : Two (vlay p STK σ₁) vWb STK x y :=
  ⟨h₁.site, vlay_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

/-- Two runs whose entry states have the same layout. -/
def VTwo (p : Params) (STK : Nat) (x y : State) : Prop := ∃ σ, Two (vlay p STK σ) vWb STK x y

theorem vtaint7 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r7]) c hc).isSome = true) : RelCT isa (VTwo p STK) c fun _ _ => True :=
  RelCT.exists_ fun _ => taint7 (fun _ _ h => h) h

theorem vtaint4 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r4, .r5, .r6, .r7]) c hc).isSome = true) :
    RelCT isa (VTwo p STK) c fun _ _ => True :=
  RelCT.exists_ fun _ => taint4 (fun _ _ h => h) h

/-- A piece without calls, checked by the taint analysis from `scratch`. -/
theorem vrel7 {p : Params} {STK : Nat} {I : State → State → Prop} (hI : ∀ σ s, I σ s → VC p STK σ s)
    {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r7]) c hc).isSome = true) :
    RelCT isa (Rel2 (VPre p STK) (vPub p) I) c fun _ _ => True :=
  rel_of (vtaint7 h) fun σ₁ _ _ _ _ _ pub h₁ h₂ => ⟨σ₁, vc_twoL pub (hI _ _ h₁) (hI _ _ h₂)⟩

/-! ## The state, but for a register or the flags -/

theorem VC.r11 {p : Params} {STK : Nat} {σ s : State} (h : VC p STK σ s) (v : BitVec 32) :
    VC p STK σ (s.setReg .r11 v) :=
  ⟨h.site.setReg (by decide) v, h.rd, h.wr, h.sp, h.sav, h.lr, h.pk, h.mu, h.sg⟩

/-! ## A branch on `r11` -/

theorem cmp11_ok (s : State) :
    WP isa (.block [.cmp .r11 (.imm 0)]) s (· = subFlags s (s.gpr .r11) 0) := by
  apply WP.of_runBlock
  simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Op2.eval,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']

theorem eval_cmp11 (s : State) : isa.eval .ne (subFlags s (s.gpr .r11) 0) = some (decide (s.gpr .r11 ≠ 0)) := by
  show some (!(s.gpr .r11 - 0 == 0)) = _
  rw [show s.gpr .r11 - 0 = s.gpr .r11 from by simp]
  by_cases h : s.gpr .r11 = 0
  · simp [h]
  · rw [beq_eq_false_iff_ne.mpr h]; simp only [Bool.not_false, Option.some.injEq]; exact (decide_eq_true h).symm

/-- `ifOk c`: `c` if `r11 ≠ 0`, where `r11` is `v σ`, a function of the
public data. -/
theorem ifOk_piece {p : Params} {STK : Nat} {I J : State → State → Prop} {c : Prog isa} {v : State → BitVec 32}
    (hv : ∀ σ s, VPre p STK σ → I σ s → s.gpr .r11 = v σ)
    (hpub : ∀ σ₁ σ₂, VPre p STK σ₁ → VPre p STK σ₂ → vPub p σ₁ σ₂ → v σ₁ = v σ₂)
    (hI : ∀ σ s (a b : BitVec 32), I σ s → I σ (subFlags s a b))
    (hc : VPiece p STK (fun σ s => I σ s ∧ v σ ≠ 0) J c)
    (he : ∀ σ s, VPre p STK σ → I σ s → v σ = 0 → J σ s) :
    VPiece p STK I J (ifOk c) := by
  refine ⟨fun σ s hp hs => WP.seq (WP.mono (cmp11_ok s) fun s₁ e₁ => ?_), ?_⟩
  · subst e₁
    have h11 := hv σ s hp hs
    refine WP.ite _ (eval_cmp11 s) (fun hb => hc.ok σ _ hp ⟨hI σ s _ _ hs, ?_⟩) fun hb => ?_
    · rw [← h11]; exact of_decide_eq_true hb
    · have : v σ = 0 := by rw [← h11]; simpa using hb
      exact WP.block_nil (he σ _ hp (hI σ s _ _ hs) this)
  · refine RelCT.seq (R := Rel2 (VPre p STK) (vPub p) fun σ s => ∃ s₀, I σ s₀ ∧ s = subFlags s₀ (s₀.gpr .r11) 0)
      ?_ (RelCT.ite ?_ ?_ ?_)
    · refine relInv (I' := fun σ s => ∃ s₀, I σ s₀ ∧ s = subFlags s₀ (s₀.gpr .r11) 0)
        (fun σ s _ hs => WP.mono (cmp11_ok s) fun s' e => ⟨s, hs, e⟩) ?_
      exact relct_noMem (by decide)
    · rintro _ _ ⟨σ₁, σ₂, p₁, p₂, pub, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩
      rw [eval_cmp11, eval_cmp11, hv _ _ p₁ hx, hv _ _ p₂ hy, hpub _ _ p₁ p₂ pub]
    · refine RelCT.mono hc.tr (fun _ _ ⟨⟨σ₁, σ₂, p₁, p₂, pub, ⟨x, hx, e₁⟩, ⟨y, hy, e₂⟩⟩, hb⟩ =>
        ⟨σ₁, σ₂, p₁, p₂, pub, ⟨e₁ ▸ hI _ _ _ _ hx, ?_⟩, ⟨e₂ ▸ hI _ _ _ _ hy, ?_⟩⟩) fun _ _ h => h
      · subst e₁; rw [eval_cmp11] at hb
        rw [← hv _ _ p₁ hx]; simpa using hb
      · subst e₁ e₂; rw [eval_cmp11] at hb
        rw [← hpub _ _ p₁ p₂ pub, ← hv _ _ p₁ hx]; simpa using hb
    · exact RelCT.block_nil fun _ _ _ => trivial

end VG.Proof.MlDsa.Arm.Verify
