import VerifiedGarbage.Proof.CmacAes.Stream.X86.Absorb

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_absorb` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
`esp`, the stack arguments and `ebp`, which the correctness proof pins to a
value of the public arguments (`AAft`), and each call of `vg_cmac_aes_update`,
in its frame, is constant time by its own proof (`upd_rel`), its arguments
pinned by `AMid₁` and `AMid₂`.
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbX86.pre s₀) (h0' : absorbX86.pre s₀')
    (hq : absorbX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (absorb v.callee v.suffix) fun _ _ => True := by
  have hp := APre.of h0
  have hp' := APre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have eSt : aSt s₀ = aSt s₀' := qa 0 (by decide)
  have eR : aR s₀ = aR s₀' := by rw [aR, aR, qa 1 (by decide)]
  have eC : aC s₀ = aC s₀' := by rw [aC, aC, countX86, countX86, qa 2 (by decide), qa 3 (by decide)]
  have eD : aD s₀ = aD s₀' := qa 4 (by decide)
  have eL : aL s₀ = aL s₀' := by rw [aL, aL, qa 5 (by decide)]
  have eS : aSc s₀ = aSc s₀' := qa 6 (by decide)
  have e2 : d2Of s₀ = d2Of s₀' := by rw [d2Of, d2Of, eC, eL, eSt, eD]
  have ag : ∀ {rs : List Reg} {a b : State}, Pt 7 s₀ a → Pt 7 s₀' b → (∀ r ∈ rs, a.gpr r = b.gpr r) →
      VG.X86.Taint.Agree (argTaint rs (4 + 4 * 7)) a b :=
    fun h₁ h₂ hr => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ hr
  have bp : ∀ {v v' : Nat} {a b : State}, v = v' → AAft s₀ v a → AAft s₀' v' b → ∀ r ∈ [Reg.ebp], a.gpr r = b.gpr r :=
    fun e h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ebp, h₂.ebp, e]
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 7))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _) fun r hr => by simp at hr)
    (c := absorbPre) (by taint_decide)).wp (F₁ := AMid₁ s₀) (F₂ := AMid₁ s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨absorbPre_wp hp, absorbPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have c₁ := ((upd_rel v (E := aE s₀) (P := fun a b => AMid₁ s₀ a ∧ AMid₁ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [eSt, eS, eR, eC, eL]; exact h.2.args, h.1.ctx.esp,
        by rw [h.2.ctx.esp]; exact qE.symm⟩).wp
      (F₁ := AAft s₀ (fOf (aC s₀) (aL s₀))) (F₂ := AAft s₀' (fOf (aC s₀') (aL s₀')))
      fun _ _ h => ⟨(call1_after v) hp h.1, (call1_after v) hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have m := ((RelCT.taint (A := taint) (P := fun a b => AAft s₀ (fOf (aC s₀) (aL s₀)) a ∧
      AAft s₀' (fOf (aC s₀') (aL s₀')) b) (argTaint [.ebp] (4 + 4 * 7))
    (fun _ _ h => ag h.1.ctx.pt h.2.ctx.pt (bp (by rw [eC, eL]) h.1 h.2))
    (c := chain2) (by taint_decide)).wp (F₁ := AMid₂ s₀) (F₂ := AMid₂ s₀')
    fun _ _ h => ⟨WP.mono (chain2_mid hp h.1) fun _ h => h.1, WP.mono (chain2_mid hp' h.2) fun _ h => h.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have c₂ := ((upd_rel v (E := aE s₀) (P := fun a b => AMid₂ s₀ a ∧ AMid₂ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [eSt, eS, eR, eC, eL, e2]; exact h.2.args, h.1.aft.ctx.esp,
        by rw [h.2.aft.ctx.esp]; exact qE.symm⟩).wp
      (F₁ := AAft s₀ (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀)))
      (F₂ := AAft s₀' (fOf (aC s₀') (aL s₀') + 16 * nbOf (aC s₀') (aL s₀')))
      fun _ _ h => ⟨(call2_after v) hp h.1, (call2_after v) hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have p := RelCT.taint (A := taint) (P := fun a b => AAft s₀ (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀)) a ∧
      AAft s₀' (fOf (aC s₀') (aL s₀') + 16 * nbOf (aC s₀') (aL s₀')) b) (argTaint [.ebp] (4 + 4 * 7))
    (fun _ _ h => ag h.1.ctx.pt h.2.ctx.pt (bp (by rw [eC, eL]) h.1 h.2)) (c := absorbPost) (by taint_decide)
  exact a.seq (c₁.seq (m.seq (c₂.seq p)))

theorem absorb_ct : ConstantTime isa absorbX86.pre absorbX86.pub (absorb v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => ((absorb_rel v) h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86
