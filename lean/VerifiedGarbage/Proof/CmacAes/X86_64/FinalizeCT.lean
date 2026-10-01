import VerifiedGarbage.Proof.CmacAes.X86_64.FinalizeCorrect
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_finalize` is constant time

Untrusted: everything here is checked by Lean. The code before the call is
checked by the taint analysis (its branches and the copy loop depend only on
`last_len`), and the call of `vg_aes_ctr32` is constant time by its own proof
(`ctr_rel`), its arguments pinned by the correctness proof (`FMid`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem finalize_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : finalizeX86_64.pre s₀)
    (h0' : finalizeX86_64.pre s₀') (hq : finalizeX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finalize v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := FPre.of h0
  have hp' : FPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat
      (s₀.gpr .rsi).toNat := by
    rw [q1, q2, q3, q4, q5, q6]; exact FPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := FMid s₀ _ _ _ _ _ _) (F₂ := FMid s₀' _ _ _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩
  have c := ctr_rel v (P := fun s₁ s₂ =>
      FMid s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat s₁ ∧
      FMid s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat s₂)
    fun s₁ s₂ h => ⟨_, _, _, _, _, h.1.pre, h.2.pre, by
      rw [h.1.saved _ (by simp [calleeSaved]), h.2.saved _ (by simp [calleeSaved]), q7]⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq c

theorem finalize_ct (v : Ctr32Impl) :
    ConstantTime isa finalizeX86_64.pre finalizeX86_64.pub (finalize v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalize_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86_64
