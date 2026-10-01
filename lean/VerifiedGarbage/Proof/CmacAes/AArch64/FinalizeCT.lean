import VerifiedGarbage.Proof.CmacAes.AArch64.FinalizeCorrect
import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCT

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_finalize` is constant time

Untrusted: everything here is checked by Lean. The code before the call is
checked by the taint analysis (its branches and the copy loop depend only on
`last_len`), the call of `vg_aes_ctr32` is constant time by its own proof
(`ctr_rel`), its arguments pinned by the correctness proof (`FMid`), and the
restore after it by the taint analysis again, from `x19` (the scratch buffer).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

theorem finalize_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : finalizeAArch64.pre s₀)
    (h0' : finalizeAArch64.pre s₀') (hq : finalizeAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finalize v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := FPre.of h0
  have hp' : FPre s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat
      (s₀.gpr .x1).toNat := by
    rw [q1, q2, q3, q4, q5, q6]; exact FPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19])
      (.block [.ldr .x .x30 .x19 2072, .ldr .x .x19 .x19 2064]) h).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q7 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := FMid s₀ _ _ _ _ _ _) (F₂ := FMid s₀' _ _ _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩
  have c := (ctr_rel v (P := fun s₁ s₂ =>
      FMid s₀ (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat s₁ ∧
      FMid s₀' (s₀.gpr .x0) (s₀.gpr .x2) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat s₂)
    fun s₁ s₂ h => ⟨h.1.pre, h.2.pre, by rw [h.1.sp, h.2.sp, q7]⟩).wp
    (F₁ := fun (s : State) => s.gpr .x19 = s₀.gpr .x5 ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .x19 = s₀.gpr .x5 ∧ s.sp = s₀'.sp) fun s₁ s₂ h =>
      ⟨WP.mono (ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.1.x19], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .x19 (by simp [preserved]) (by decide), h.2.x19], by rw [hc.sp, h.2.sp]⟩⟩
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (s₁.gpr .x19 = s₀.gpr .x5 ∧ s₁.sp = s₀.sp) ∧ (s₂.gpr .x19 = s₀.gpr .x5 ∧ s₂.sp = s₀'.sp)) _
    (fun s₁ s₂ h => agree_of (by rw [h.1.2, h.2.2, q7]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1, h.2.1]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem finalize_ct (v : Ctr32Impl) :
    ConstantTime isa finalizeAArch64.pre finalizeAArch64.pub (finalize v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalize_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.AArch64
