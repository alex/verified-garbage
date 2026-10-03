import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# x86 SIMD: constant-time analysis

This extends the checked scalar analysis without changing its domain or
agreement relation. SIMD values are secret, and register-only SIMD operations
cannot change any general-purpose register, flag or memory. Loads must use
public addresses; stores use the existing checked secret-store rule for sixteen
bytes.
-/
namespace VG.X86.SseTaint
open VG.X86.Taint

/-- SIMD operations alter only SIMD registers, which the analysis does not track. -/
theorem XOp.exec_eq (op : XOp) (s : State) :
    op.exec s = { s with xmm := (op.exec s).xmm } := by
  cases op <;> rfl

theorem agree_withXmm {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (x₁ x₂ : XReg → BitVec 128) :
    Agree τ { s₁ with xmm := x₁ } { s₂ with xmm := x₂ } :=
  ha.keep ha.rf rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ha.wf₁.bases ha.wf₂.bases

/-- Scalar instructions retain the existing transfer function. -/
def step (τ : T) : Instr → Option T
  | .movdquLoad _ m => if memPub τ m then some τ else none
  | .movdquStore m _ => storeStepK τ m 16 false []
  | .xop _ => some τ
  | i => Taint.stepK τ i

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (hs : step τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | mov | store | alu | shift | bswap | movzx8 | store8 | mul | push | pop | alloc | free =>
    simp only [step] at hs
    exact Taint.step_sound ha (Taint.stepK_eq ▸ hs) e₁ e₂
  | movdquLoad d m =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hm; cases hs
    simp only [exec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨v₁, -, rfl⟩ := e₁; obtain ⟨v₂, -, rfl⟩ := e₂
    exact ⟨by simp only [addrs, ha.ea hm], agree_withXmm ha _ _⟩
  | movdquStore m r =>
    simp only [step, storeStepK_eq, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hm; cases hs
    refine ⟨by simp only [addrs, ha.ea hm], ?_⟩
    simp only [exec, State.store128] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    rename_i h₁ h₂
    cases e₁; cases e₂
    exact ha.store (n := 16) hm (by decide) (fun hp => by cases hp) h₁ h₂
      (fun _ h => (List.not_mem_nil h).elim) (fun _ h => (List.not_mem_nil h).elim)
  | xop op =>
    simp only [step, Option.some.injEq] at hs
    subst hs
    simp only [exec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    rw [XOp.exec_eq op s₁, XOp.exec_eq op s₂]
    exact ⟨rfl, agree_withXmm ha _ _⟩

end VG.X86.SseTaint

namespace VG.X86

/-- Checked scalar and SIMD analysis, sharing the scalar domain and all call rules. -/
def sseTaint : VG.Taint isa := { taint with
  step := SseTaint.step
  step_sound := SseTaint.step_sound }

end VG.X86
