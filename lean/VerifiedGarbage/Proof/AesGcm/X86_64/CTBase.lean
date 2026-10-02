import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-GCM on x86-64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs piece by piece (`RelCT`): the code between the calls is
checked by the taint analysis, from registers that agree in the two runs
(`rel_taint`), and leaves registers and flags that agree for the next piece,
a branch or a loop (`rel_regs`); what correctness says about each run is
added with `rel_wp`, and the environment's registers, which no instruction
writes, keep their values (`rel_env`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64

/-- Code the taint analysis checks from registers `rs` that agree, leaving
the registers `rs'` and, if `f`, the flags agreeing. -/
theorem rel_regs {P : State → State → Prop} {c : Prog isa} (rs rs' : List Reg) (f : Bool)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, ((taint.check (Taint.ofRegs rs) c hc).map fun τ' =>
      (RegSet.ofList rs').subset τ'.regs && (!f || τ'.flags)) = some true) :
    RelCT isa P c fun s₁ s₂ => (∀ r ∈ rs', s₁.gpr r = s₂.gpr r) ∧
      (f = true → s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of) := by
  obtain ⟨_, h⟩ := hc
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (Taint.agree_ofRegs (hag _ _ hP)) e₁ e₂
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hs
  refine ⟨ht, fun r hr => ha.rf.1 r (RegSet.mem_of_subset hs.1 (RegSet.mem_ofList.mpr hr)), fun hf => ?_⟩
  exact ha.rf.2 (hs.2.resolve_left (by simp [hf]))

/-- Code the taint analysis checks from registers `rs` that agree. -/
theorem rel_taint {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s₁ s₂ h => Taint.agree_ofRegs (hag _ _ h)) hc

/-- What each run satisfies by correctness. -/
theorem rel_wp {P Q : State → State → Prop} {c : Prog isa} {F₁ F₂ G₁ G₂ : State → Prop}
    (h : RelCT isa P c Q) (hP : ∀ s₁ s₂, P s₁ s₂ → F₁ s₁ ∧ F₂ s₂)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa P c fun s₁ s₂ => Q s₁ s₂ ∧ G₁ s₁ ∧ G₂ s₂ :=
  h.wp fun _ _ hp => ⟨hw₁ _ (hP _ _ hp).1, hw₂ _ (hP _ _ hp).2⟩

/-- The environment, after code that writes none of its registers. -/
theorem rel_env {Ctx St W SP : Addr} {P Q : State → State → Prop} {c : Prog isa}
    (hc : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], ∀ i ∈ instrs c, Taint.clobbers i r = false)
    (hP : ∀ s₁ s₂, P s₁ s₂ → Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂) (h : RelCT isa P c Q) :
    RelCT isa P c fun s₁ s₂ => Q s₁ s₂ ∧ Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂ := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨r₁, w₁⟩ := Exec.rdwr e₁
  obtain ⟨r₂, w₂⟩ := Exec.rdwr e₂
  exact ⟨ht, hq, (hP _ _ hp).1.keep (fun r hr => Exec.gpr (hc r hr) e₁) r₁ w₁,
    (hP _ _ hp).2.keep (fun r hr => Exec.gpr (hc r hr) e₂) r₂ w₂⟩

/-- A branch on ZF, which agrees in the two runs. -/
theorem rel_ite_e {P Q : State → State → Prop} {t e : Prog isa} (hc : ∀ s₁ s₂, P s₁ s₂ → s₁.zf = s₂.zf)
    (ht : RelCT isa (fun s₁ s₂ => P s₁ s₂ ∧ s₁.zf = some true) t Q)
    (he : RelCT isa (fun s₁ s₂ => P s₁ s₂ ∧ s₁.zf = some false) e Q) :
    RelCT isa P (.ite .e t e) Q :=
  RelCT.ite (fun s₁ s₂ h => hc s₁ s₂ h) ht he

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64

/-- `a; (b; (c; (d; e)))`, related as `(a; (b; (c; d))); e`. -/
theorem rel_reassoc4 {P Q : State → State → Prop} {a b c d e : Prog isa}
    (h : RelCT isa P (.seq (.seq a (.seq b (.seq c d))) e) Q) : RelCT isa P (.seq a (.seq b (.seq c (.seq d e)))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with | seq d₁ f₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with | seq d₂ f₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ d₁))) f₁) (.seq (.seq a₂ (.seq b₂ (.seq c₂ d₂))) f₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- `a; (b; c)`, related as `(a; b); c`. -/
theorem rel_reassoc2 {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq (.seq a b) c) Q) : RelCT isa P (.seq a (.seq b c)) Q := RelCT.assoc h

/-- The taint check of `ghash1 yo b o`'s arguments. -/
def Gh1Check (yo : Nat) (b : Reg) (o : Nat) : Prop :=
  ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15, .rsp]) (.block (Impl.AesGcm.X86_64.ptr .rdi .r13 240 ++
    Impl.AesGcm.X86_64.ptr .rsi .r14 yo ++ Impl.AesGcm.X86_64.ptr .rdx b o ++
    [.mov32 .rcx (Impl.AesGcm.X86_64.imm 1)] ++ Impl.AesGcm.X86_64.ptr .r8 .r15 Impl.AesGcm.X86_64.scrO)) hc).isSome = true

theorem gh1Check_r14_32 {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : Gh1Check yo .r14 32 := by
  rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem gh1Check_r15_96 {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : Gh1Check yo .r15 96 := by
  rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.X86_64
