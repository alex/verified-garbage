import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseACT

/-!
# ML-DSA signing on ARMv7: constant time

Untrusted: everything here is checked by Lean. Two runs whose entry states
agree on `signK`'s public data (`signLeakT` among them) leak the same: the
prologue and the return only the pointers, `ExpandA` only `ρ`
(`expandA_tr`), and the rest what `signLeakT` says after `ρ`, on which they
agree once `ExpandA` finished (`pub_leq`, `rest_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem relStart {Pre : State → Prop} {Pub : State → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Rel2 Pre Pub fun σ s => s = σ) c Q) : ConstantTime isa Pre Pub c :=
  RelCT.constantTime (RelCT.mono h (fun s₁ s₂ ⟨p₁, p₂, hp⟩ => ⟨s₁, s₂, p₁, p₂, hp, rfl, rfl⟩) fun _ _ h => h)

theorem ldrSp_one {s u : State} {a : List Leak} (h : execBlock isa [.ldrSp .r12 0] s = some (u, a)) :
    a = [Leak.addr (State.addr (s.sp + BitVec.ofNat 32 0))] ∧ u.gpr .r12 = stackArg s 0 := by
  simp only [execBlock] at h
  split at h
  · cases h
  · rename_i s' hs
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.append_nil] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_⟩
    simp only [isa, exec, State.load32, show (0 : Nat) < 4096 from by decide, ite_true] at hs
    split at hs
    · simp only [Option.map_some, Option.some.injEq] at hs
      subst hs
      simp [State.setReg, stackArg, stackArgAddr]
    · cases hs

/-- The prologue leaks only the stack pointer and the pointer to `scratch` it loads. -/
theorem pro_tr {P : State → State → Prop} (hP : ∀ x y, P x y → x.sp = y.sp ∧ stackArg x 0 = stackArg y 0) :
    RelCT isa P (.block pro) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨hsp, harg⟩ := hP _ _ hp
  rw [Exec.block_iff, pro_eq, List.append_assoc, execBlock_append] at e₁ e₂
  obtain ⟨⟨u₁, a₁⟩, h₁, g₁⟩ := Option.bind_eq_some_iff.mp e₁
  obtain ⟨⟨u₂, a₂⟩, h₂, g₂⟩ := Option.bind_eq_some_iff.mp e₂
  obtain ⟨⟨v₁, b₁⟩, f₁, k₁⟩ := Option.map_eq_some_iff.mp g₁
  obtain ⟨⟨v₂, b₂⟩, f₂, k₂⟩ := Option.map_eq_some_iff.mp g₂
  simp only [Prod.mk.injEq] at k₁ k₂
  obtain ⟨ea₁, r₁⟩ := ldrSp_one h₁
  obtain ⟨ea₂, r₂⟩ := ldrSp_one h₂
  refine ⟨?_, trivial⟩
  rw [← k₁.2, ← k₂.2, ea₁, ea₂, hsp, execBlock_tr (rs := [.r12]) (by decide) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [r₁, r₂, harg]) f₁ f₂]

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
    ConstantTime isa (signK p D).pre (signK p D).pub (Impl.MlDsa.Arm.Sign.sign P p) := by
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hc
  have hf' := hf
  simp only [fChk, Bool.and_eq_true, decide_eq_true_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨st0, fa0⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hsz⟩ := hf'
  refine relStart (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.Arm.Sign.sign
  refine RelCT.seq (RelCT.mono (relInvE (J := fun σ s => St p D σ s ∧ s.gpr .r11 = 1) (E := fun _ _ => True)
    (fun σ s hp hs => by
      subst hs
      exact WP.mono (pro_ok hp) fun s₁ ⟨h₁, hf₁, h15⟩ => ⟨entry_st h3 hp h₁ hf₁, h15⟩)
    (pro_tr fun x y ⟨⟨σ₁, σ₂, _, _, hpub, h₁, h₂⟩, _⟩ => by
      subst h₁ h₂
      exact ⟨hpub.2.2.2.2.2.1, hpub.2.2.2.2.1⟩)) (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (expandA_tr hP ha) ?_
  refine RelCT.seq (Q := fun _ _ => True) (R := fun (x y : State) => ∀ r ∈ [Reg.r7], x.gpr r = y.gpr r) ?_
    (VG.Proof.MlKem.Arm.taint_prog [.r7] (fun x y h => h) (by taint_decide))
  unfold ifOk
  refine ifOkElse_tr (D := D) (P := RA p D (p.k * p.ℓ)) (fun x y h => by rw [h.2]) (RelCT.mono (rest_tr hP h3)
    (fun x y ⟨x₀, y₀, ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, h15⟩, ⟨hPx, _, _⟩, ⟨hPy, _, _⟩, hne⟩ => ?_)
    fun x y h => lrel_r7 (h.lrel fun _ _ h => h.st))
    (RelCT.mono nil_tr (fun _ _ h => h) fun x y h =>
      ifOk_r7 (I := fun σ s => IA p D σ (p.k * p.ℓ) s) (fun _ _ h => h.st) (E := fun _ _ => True)
        (C := fun x₀ => x₀.gpr .r11 = 0)
        (by obtain ⟨x₀, y₀, R, hx, hy, h0⟩ := h; exact ⟨x₀, y₀, rr_rs R, hx, hy, h0⟩))
  have e₁ := r11_one i₁.r01 hne
  have e₂ : y₀.gpr .r11 = 1 := h15 ▸ e₁
  obtain ⟨ok₁, fam₁⟩ := i₁.ok e₁
  obtain ⟨ok₂, fam₂⟩ := i₂.ok e₂
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, pub_leq hpub (expandA_max ok₁) (expandA_max ok₂),
    ⟨i₁.st.step hPx st0, ok₁, Fam.keep i₁.st.lay hPx fa0 fam₁⟩,
    ⟨i₂.st.step hPy st0, ok₂, Fam.keep i₂.st.lay hPy fa0 fam₂⟩⟩

end

end VG.Proof.MlDsa.Arm.Sign
