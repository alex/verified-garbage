import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.RelCT

/-!
# AES-GCM on AArch64: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs relate
two runs from given states (`Eq2 σ₁ σ₂`) piece by piece: the code between
calls by the taint analysis, from the registers the correctness proofs pin to
the same public values in both runs (`rel_taint`); each call by its callee's
proof (`rel_gh`, `rel_ctr`, `rel_key`); a branch on a value both runs agree
on (`rel_ite`); and the next piece from the states the correctness proofs
describe (`rel_seq`). A block may be split where the taint analysis needs a
register pinned anew (`RelCT.block_split`).
-/

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

theorem execBlock_append (l₁ l₂ : List Instr) (s : State) {s' : State} {t : List Leak}
    (h : execBlock isa (l₁ ++ l₂) s = some (s', t)) :
    ∃ s₁ t₁ t₂, execBlock isa l₁ s = some (s₁, t₁) ∧ execBlock isa l₂ s₁ = some (s', t₂) ∧ t = t₁ ++ t₂ := by
  induction l₁ generalizing s t with
  | nil => exact ⟨s, [], t, rfl, h, rfl⟩
  | cons i is ih =>
    simp only [List.cons_append, execBlock] at h ⊢
    cases hx : exec i s with
    | none => rw [hx] at h; cases h
    | some s₁ =>
      rw [hx] at h
      simp only at h ⊢
      obtain ⟨⟨s₂, t₂⟩, h₂, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨s₃, t₃, t₄, h₃, h₄, rfl⟩ := ih s₁ h₂
      exact ⟨s₃, List.map Leak.addr (addrs i s) ++ t₃, t₄, by simp [h₃], h₄, by simp⟩

/-- A block run as two. -/
theorem RelCT.block_split {l₁ l₂ : List Instr} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq (.block l₁) (.block l₂)) Q) : RelCT isa P (.block (l₁ ++ l₂)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      obtain ⟨a₁, u₁, v₁, x₁, y₁, rfl⟩ := execBlock_append l₁ l₂ _ h₁
      obtain ⟨a₂, u₂, v₂, x₂, y₂, rfl⟩ := execBlock_append l₁ l₂ _ h₂
      exact h _ _ _ _ _ _ hp (.seq (.block x₁) (.block y₁)) (.seq (.block x₂) (.block y₂))

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hsp : σ₁.sp = σ₂.sp)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) (hc : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨hsp, fun r h => hr r (VG.AArch64.Taint.mem_ofRegs.mp h)⟩) hc

theorem rel_gh (g : GhashImpl) {σ₁ σ₂ : State} {H Y D S : Addr} {n : Nat} (h₁ : GhCall σ₁ H Y D S n)
    (h₂ : GhCall σ₂ H Y D S n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (.call g.fn.name g.fn.code) TT :=
  gh_rel g fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨H, Y, D, S, n, h₁, h₂, hsp⟩

theorem rel_ctr (v : Ctr32Impl) {σ₁ σ₂ : State} {K C D S : Addr} {R n : Nat} (h₁ : CtrCall σ₁ K C D S R n)
    (h₂ : CtrCall σ₂ K C D S R n) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (.call v.callee.name v.callee.code) TT :=
  ctr_rel v fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩

theorem rel_key (k : KeyImpl) {σ₁ σ₂ : State} {K C S : Addr} {L : Nat} (h₁ : KeyCall σ₁ K C S L)
    (h₂ : KeyCall σ₂ K C S L) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (.call k.fn.name k.fn.code) TT :=
  key_rel k fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, S, L, h₁, h₂, hsp⟩

/-- A branch both runs take the same way. -/
theorem rel_ite {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} (e₁ : isa.eval c σ₁ = some b)
    (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (Eq2 σ₁ σ₂) t TT)
    (hf : b = false → RelCT isa (Eq2 σ₁ σ₂) e TT) : RelCT isa (Eq2 σ₁ σ₂) (.ite c t e) TT := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- Constant time, from related runs from every pair of states. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c TT) : ConstantTime isa pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.AArch64

namespace VG.Proof.AesGcm.AArch64

/-- Proves `∀ r ∈ [r₁, …], σ₁.gpr r = σ₂.gpr r` by rewriting each side with `ts`. -/
macro "agree_tac" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true, and_self, $ts,*])

end VG.Proof.AesGcm.AArch64
