import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseACT

/-!
# ML-DSA signing on AArch64: constant time

Untrusted: everything here is checked by Lean. Two runs whose entry states
agree on `signK`'s public data (`signLeakT` among them) leak the same: the
prologue and the return only the pointers, `ExpandA` only `ρ`
(`expandA_tr`), and the rest what `signLeakT` says after `ρ`, on which they
agree once `ExpandA` finished (`pub_leq`, `rest_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params} {D : Nat}

/-- Two runs whose `ExpandA` finished agree on what their loops leak. -/
theorem pub_leq {σ₁ σ₂ : State} (hpub : (signK p D).pub σ₁ σ₂)
    (hA₁ : expandA p maxBounds (rhoOf p σ₁) = some (amat p (Am p σ₁)))
    (hA₂ : expandA p maxBounds (rhoOf p σ₂) = some (amat p (Am p σ₂))) : LeakEq p 0 σ₁ σ₂ := by
  have e := hpub.2.2.2.2.2.2
  rw [signLeakT_eq hA₁, signLeakT_eq hA₂] at e
  have hρ : (skOf p σ₁).take 32 = (skOf p σ₂).take 32 := pub_rho hpub
  rw [hρ] at e
  exact List.append_cancel_left e

theorem rr_rs {I E : State → State → Prop} {x y : State} (h : RR p D I E x y) : RS p D (fun _ _ => True) I x y := by
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, _⟩ := h
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, trivial, i₁, i₂⟩

theorem sign_ct {P : Prims} (hP : PrimsOk P D) (h3 : Ok3 p) :
    ConstantTime isa (signK p D).pre (signK p D).pub (Impl.MlDsa.AArch64.Sign.sign P p) := by
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  refine relStart (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.AArch64.Sign.sign
  refine RelCT.seq (RelCT.mono (relInvE (J := fun σ s => St p D σ s ∧ s.gpr .x24 = 1) (E := fun _ _ => True)
    (fun σ s hp hs => by
      subst hs
      exact WP.mono (pro_ok (pro_in h3 hp)) fun s₁ ⟨h₁, h15, hf₁⟩ => ⟨entry_st h3 hp h₁ hf₁, h15⟩)
    (taintRel [.x0, .x1, .x2, .x3, .x4] (fun x y ⟨⟨σ₁, σ₂, _, _, hpub, h₁, h₂⟩, _⟩ => by
      subst h₁ h₂
      obtain ⟨e0, e1, e2, e3, e4, e5, -⟩ := hpub
      refine ⟨e5, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [e0, e1, e2, e3, e4]) (by taint_decide))) (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (expandA_tr hP ha) ?_
  refine RelCT.seq (Q := fun _ _ => True) (R := fun (x y : State) => LRel D (sgR p) (sgW p) x y) ?_
    (lrel_tr (fun x y h => h) (by taint_decide))
  unfold ifOk
  refine ifOkElse_tr (P := RA p D (p.k * p.ℓ)) (fun x y h => by rw [h.2]) (RelCT.mono (rest_tr hP h3)
    (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, h15⟩, hne⟩ => ?_) fun x y h => h.lrel fun _ _ h => h.st)
    (RelCT.mono nil_tr (fun _ _ h => h) fun x y h => h.1.lrel fun _ _ h => h.st)
  have e₁ := x24_one i₁.r01 hne
  have e₂ : y.gpr .x24 = 1 := h15 ▸ e₁
  obtain ⟨ok₁, fam₁⟩ := i₁.ok e₁
  obtain ⟨ok₂, fam₂⟩ := i₂.ok e₂
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, pub_leq hpub (expandA_max ok₁) (expandA_max ok₂), ⟨i₁.st, ok₁, fam₁⟩,
    ⟨i₂.st, ok₂, fam₂⟩⟩

end

end VG.Proof.MlDsa.AArch64.Sign
