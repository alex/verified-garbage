import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseACT

/-!
# ML-DSA signing on x86-64: constant time

Two runs whose entry states agree on `signK`'s public data (`signLeakT` among
them) leak the same: the prologue and the return only the pointers, `ExpandA`
only `ρ` (`expandA_tr`), and the rest what `signLeakT` says after `ρ`, on
which they agree once `ExpandA` finished (`pub_leq`, `rest_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Rel2 relStart)
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
    ConstantTime isa (signK p D).pre (signK p D).pub (Impl.MlDsa.X86_64.Sign.sign P p) := by
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hc
  have hf' := hf
  simp only [fChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨st0, fa0⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hsz⟩ := hf'
  refine relStart (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.X86_64.Sign.sign
  refine RelCT.seq (RelCT.mono (relInvE (J := fun σ s => St p D σ s ∧ s.gpr .r15 = 1) (E := fun _ _ => True)
    (fun σ s hp hs => by
      subst hs
      exact WP.mono (pro_ok hp hsz.1) fun s₁ ⟨h₁, _, hf₁, h15⟩ => ⟨entry_st hP h3 hp h₁ hf₁, h15⟩)
    (block_tr (rs := [.r8]) rfl fun x y ⟨⟨σ₁, σ₂, _, _, hpub, h₁, h₂⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr h₁ h₂
      exact hpub.2.2.2.2.1)) (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (expandA_tr hP ha) ?_
  refine RelCT.seq (Q := fun _ _ => True) (R := fun (x y : State) => ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) ?_
    (VG.Proof.MlKem.X86_64.taintRel [.rbx] (fun x y h => h) (by taint_decide))
  unfold ifOk
  refine ifOkElse_tr (D := D) (P := RA p D (p.k * p.ℓ)) (fun x y h => by rw [h.2]) (RelCT.mono (rest_tr hP h3)
    (fun x y ⟨x₀, y₀, ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, h15⟩, ⟨hPx, _, _⟩, ⟨hPy, _, _⟩, hne⟩ => ?_)
    fun x y h => lrel_rbx (h.lrel fun _ _ h => h.st))
    (RelCT.mono nil_tr (fun _ _ h => h) fun x y h =>
      ifOk_rbx (I := fun σ s => IA p D σ (p.k * p.ℓ) s) (fun _ _ h => h.st) (E := fun _ _ => True)
        (C := fun x₀ => (x₀.gpr .r15).setWidth 32 = 0)
        (by obtain ⟨x₀, y₀, R, hx, hy, h0⟩ := h; exact ⟨x₀, y₀, rr_rs R, hx, hy, h0⟩))
  have e₁ := r15_one i₁.r01 hne
  have e₂ : y₀.gpr .r15 = 1 := h15 ▸ e₁
  obtain ⟨ok₁, fam₁⟩ := i₁.ok e₁
  obtain ⟨ok₂, fam₂⟩ := i₂.ok e₂
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, pub_leq hpub (expandA_max ok₁) (expandA_max ok₂),
    ⟨i₁.st.step hPx st0, ok₁, Fam.keep i₁.st.lay hPx fa0 fam₁⟩,
    ⟨i₂.st.step hPy st0, ok₂, Fam.keep i₂.st.lay hPy fa0 fam₂⟩⟩

end

end VG.Proof.MlDsa.X86_64.Sign
