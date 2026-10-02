import VerifiedGarbage.Proof.AesGcm.Arm.Init
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_init` is constant time

Untrusted: everything here is checked by Lean. The blocks are checked by the
taint analysis, from the registers the correctness proof pins (the
arguments, then `r8`, `r9` and `r11`); the calls of `vg_aes_expand_key` and
`vg_aes_ctr32` are constant time by their own proofs (`key_rel`, `ctr_rel`),
with the same arguments in both runs.
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

theorem IS4.r11 {s₀ s₄ : State} (h : initArm.pre s₀) (h4 : IS4 s₀ s₄) : s₄.gpr .r11 = s₀.gpr .r3 := by
  obtain ⟨s₃, h3, cp⟩ := h4
  obtain ⟨-, -, -, -, -, -, -, -, -, g11, -⟩ := h3.facts h
  rw [cp.saved _ (by decide) (by decide), g11]

theorem init_rel {s₀ s₀' : State} (h0 : initArm.pre s₀) (h0' : initArm.pre s₀') (hq : initArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄⟩ := hq
  have eR : initR s₀' = initR s₀ := by simp only [initR, q₂]
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := IS1 s₀) (G' := IS1 s₀') (c := .block initPre)
    (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s s' e e' => by
      subst e e'
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> assumption) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact is1_wp h0) (fun s e => by rw [e]; exact is1_wp h0')
  have b := rel_wp (F := IS1 s₀) (F' := IS1 s₀') (G := IS2 s₀) (G' := IS2 s₀')
    (key_rel fun s₁ s₂ h => ⟨_, _, _, _, init_kc h0 h.1, by have := init_kc h0' h.2; rwa [← q₁, ← q₂, ← q₃, ← q₄] at this⟩)
    (fun s₁ h1 => WP.mono (key_call (init_kc h0 h1)) fun s₂ kp => ⟨s₁, h1, kp⟩)
    (fun s₁ h1 => WP.mono (key_call (init_kc h0' h1)) fun s₂ kp => ⟨s₁, h1, kp⟩)
  have c := rel_agree (F := IS2 s₀) (F' := IS2 s₀') (G := IS3 s₀) (G' := IS3 s₀') (c := .block initArgs)
    (Taint.ofRegs [.r8, .r9, .r11])
    (fun s s' e e' => by
      obtain ⟨g9, g11, g8, -⟩ := e.g
      obtain ⟨g9', g11', g8', -⟩ := e'.g
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [g8, g8', q₂]
      · rw [g9, g9', q₃]
      · rw [g11, g11', q₄]) ⟨_, by taint_decide⟩
    (fun s e => by obtain ⟨s₃, run⟩ := is3_run h0 e; exact WP.of_runBlock ⟨s₃, run, s, e, run⟩)
    (fun s e => by obtain ⟨s₃, run⟩ := is3_run h0' e; exact WP.of_runBlock ⟨s₃, run, s, e, run⟩)
  have d := rel_wp (F := IS3 s₀) (F' := IS3 s₀') (G := IS4 s₀) (G' := IS4 s₀')
    (ctr_rel fun s₁ s₂ h => ⟨_, _, _, _, _, _, init_cc h0 h.1,
      by have := init_cc h0' h.2; rwa [← q₃, ← q₄, eR] at this,
      by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, e⟩ := h.1.facts h0
         obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, e'⟩ := h.2.facts h0'
         rw [e, e', q₀]⟩)
    (fun s₃ h3 => WP.mono (ctr_call (init_cc h0 h3)) fun s₄ cp => ⟨s₃, h3, cp⟩)
    (fun s₃ h3 => WP.mono (ctr_call (init_cc h0' h3)) fun s₄ cp => ⟨s₃, h3, cp⟩)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have e := RelCT.taint (A := taint) (P := fun s₁ s₂ => IS4 s₀ s₁ ∧ IS4 s₀' s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r11 h0, h.2.r11 h0', q₄]) hB
  exact a.seq (b.seq (c.seq (d.seq e)))

theorem init_ct : ConstantTime isa initArm.pre initArm.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm
