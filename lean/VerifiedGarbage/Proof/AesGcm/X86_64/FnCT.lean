import VerifiedGarbage.Proof.AesGcm.X86_64.Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptCT
import VerifiedGarbage.Proof.AesGcm.X86_64.J0CT

/-!
# AES-GCM on x86-64: functions in two runs

Untrusted: everything here is checked by Lean. A function is its entry,
checked by the taint analysis from the public arguments, after which
correctness says what each run holds (`I₁`, `I₂`); its body, related from
those; and `restore`, checked from the environment the body leaves
(`fn_rel`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

theorem restore_check : ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp]) (.block restore) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A function `entry; body; restore`, in two runs from `s₀` and `s₀'`. -/
theorem fn_rel {E : List Instr} {B : Prog isa} {s₀ s₀' : State} {I₁ I₂ : State → Prop} {Ctx St W SP : Addr}
    (rs : List Reg) (hag : ∀ r ∈ rs, s₀.gpr r = s₀'.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) (.block E) hc).isSome = true)
    (hE₁ : WP isa (.block E) s₀ I₁) (hE₂ : WP isa (.block E) s₀' I₂)
    (hB : RelCT isa (fun s₁ s₂ => True ∧ I₁ s₁ ∧ I₂ s₂) B
      fun s₁ s₂ => Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.seq (.block E) (.seq B (.block restore))) fun _ _ => True := by
  have e := rel_wp (rel_taint (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') rs (fun _ _ h => by
      obtain ⟨rfl, rfl⟩ := h; exact hag) hc) (fun _ _ h => h) (G₁ := I₁) (G₂ := I₂)
    (fun s h => h ▸ hE₁) (fun s h => h ▸ hE₂)
  exact RelCT.seq e (RelCT.seq hB (rel_taint [.r13, .r14, .r15, .rsp]
    (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.1, h.2, fun _ h => by cases h⟩) restore_check))

/-- Constant time, from runs related from each pair of states. -/
theorem ct_of_rel {k : Contract isa} {c : Prog isa}
    (h : ∀ s₀ s₀', k.pre s₀ → k.pre s₀' → k.pub s₀ s₀' →
      RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') c fun _ _ => True) :
    ConstantTime isa k.pre k.pub c :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (h _ _ h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.X86_64
