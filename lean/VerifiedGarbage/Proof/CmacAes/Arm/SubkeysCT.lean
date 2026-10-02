import VerifiedGarbage.Proof.CmacAes.Arm.Subkeys
import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCT

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_subkeys` is constant time

The code before the call and after it is checked by the taint analysis, from
the registers the correctness proof pins (the arguments, then `r5` and `r6`);
the call of `vg_aes_ctr32`, in its frame, is constant time by its own proof
(`ctr_rel`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm

/-- What is known after the call. -/
structure SPost (s₀ : State) (s : State) : Prop where
  r5 : s.gpr .r5 = Sc s₀
  r6 : s.gpr .r6 = Kb s₀

theorem spost_wp {s₀ s : State} (h : SAfter s₀ s) : WP isa (ctrCall .r4 .r5) s (SPost s₀) :=
  WP.mono (ctr_call h.pre) fun _ hc =>
    ⟨by rw [hc.saved .r5 (by simp [preserved]) (by decide), h.r5],
      by rw [hc.saved .r6 (by simp [preserved]) (by decide), h.r6]⟩

theorem subkeys_rel {s₀ s₀' : State} (h0 : subkeysArm.pre s₀) (h0' : subkeysArm.pre s₀')
    (hq : subkeysArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') subkeys fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄⟩ := hq
  have hp := SPre.of h0
  have hp' := SPre.of h0'
  have eW : W s₀' = W s₀ := q₁.symm
  have eR : R s₀' = R s₀ := by rw [R, R, q₂]
  have eK : Kb s₀' = Kb s₀ := q₃.symm
  have eS : Sc s₀' = Sc s₀ := q₄.symm
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.r0, .r1, .r2, .r3]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r5, .r6]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := SAfter s₀) (G' := SAfter s₀')
    (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s s' e e' => by
      subst e e'
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> assumption) ⟨_, hA⟩
    (fun s e => by rw [e]; exact pre_wp hp) (fun s e => by rw [e]; exact pre_wp hp')
  have c := rel_wp (F := SAfter s₀) (F' := SAfter s₀') (G := SPost s₀) (G' := SPost s₀')
    (ctr_rel (sp₀ := s₀.sp) fun s₁ s₂ h =>
      ⟨h.1.pre, by have := h.2.pre; rwa [eW, eS, eK, eR] at this, h.1.sp, h.2.sp.trans q₀.symm⟩)
    (fun _ h => spost_wp h) (fun _ h => spost_wp h)
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => SPost s₀ s₁ ∧ SPost s₀' s₂) (Taint.ofRegs [.r5, .r6])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r5, h.2.r5, eS]
      · rw [h.1.r6, h.2.r6, eK]) hB
  exact a.seq (c.seq b)

theorem subkeys_ct : ConstantTime isa subkeysArm.pre subkeysArm.pub subkeys :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeys_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Arm
