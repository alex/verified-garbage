import VerifiedGarbage.Proof.Framework.X86_64.Taint.Domain

/-!
# Taint tracking for x86-64: SSE, AVX and MXCSR instructions

Untrusted: everything here is checked by Lean.

The soundness of the analysis's step (`Taint.step`) for each instruction on the
SSE and AVX registers, their loads and stores, and the MXCSR instructions and
`lfence`. The analysis does not track the vector registers or MXCSR.
-/

namespace VG.X86_64.Taint

/-- An SSE instruction on registers changes only the SSE registers. -/
theorem XOp.exec_eq (op : XOp) (s : State) : op.exec s = { s with xmm := (op.exec s).xmm } := by
  cases op <;> rfl

/-- An AVX instruction on registers changes only the vector registers. -/
theorem VOp.exec_eq (op : VOp) (s : State) :
    op.exec s = { s with xmm := (op.exec s).xmm, ymmHi := (op.exec s).ymmHi } := by
  cases op <;> simp only [VOp.exec] <;> (try split) <;> rfl

/-- Changing only the SSE registers, which the analysis does not track. -/
theorem Agree.withXmm {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) (x₁ x₂ : XReg → BitVec 128) :
    Agree τ { s₁ with xmm := x₁ } { s₂ with xmm := x₂ } :=
  ha.keep ha.rf rfl rfl rfl rfl rfl rfl ha.wf₁.2 ha.wf₂.2 ha.lo

/-- Changing only the vector registers, which the analysis does not track. -/
theorem Agree.withVec {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) (x₁ x₂ y₁ y₂ : XReg → BitVec 128) :
    Agree τ { s₁ with xmm := x₁, ymmHi := y₁ } { s₂ with xmm := x₂, ymmHi := y₂ } :=
  ha.keep ha.rf rfl rfl rfl rfl rfl rfl ha.wf₁.2 ha.wf₂.2 ha.lo

/-- Changing only MXCSR, which the analysis does not track. -/
theorem Agree.withMxcsr {τ : T} {s₁ s₂ : State} (ha : Agree τ s₁ s₂) (m₁ m₂ : BitVec 32) :
    Agree τ { s₁ with mxcsr := m₁ } { s₂ with mxcsr := m₂ } :=
  ha.keep ha.rf rfl rfl rfl rfl rfl rfl ha.wf₁.2 ha.wf₂.2 ha.lo

theorem step_sound_movdquLoad {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {d : XReg} {m : MemOp}
    (ha : Agree τ s₁ s₂) (hs : step τ (.movdquLoad d m) = some τ')
    (e₁ : exec (.movdquLoad d m) s₁ = some s₁') (e₂ : exec (.movdquLoad d m) s₂ = some s₂') :
    addrs (.movdquLoad d m) s₁ = addrs (.movdquLoad d m) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok; cases hs
  simp only [exec, Option.map_eq_some_iff] at e₁ e₂
  obtain ⟨v₁, -, rfl⟩ := e₁; obtain ⟨v₂, -, rfl⟩ := e₂
  exact ⟨by simp [addrs, ha.ea hok], ha.withXmm _ _⟩

theorem step_sound_movdquStore {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {m : MemOp} {r : XReg}
    (ha : Agree τ s₁ s₂) (hs : step τ (.movdquStore m r) = some τ')
    (e₁ : exec (.movdquStore m r) s₁ = some s₁') (e₂ : exec (.movdquStore m r) s₂ = some s₂') :
    addrs (.movdquStore m r) s₁ = addrs (.movdquStore m r) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, storeStep] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok; cases hs
  simp only [exec, State.store128] at e₁ e₂
  split at e₁ <;> [cases e₁; cases e₁]
  split at e₂ <;> [cases e₂; cases e₂]
  exact ⟨by simp [addrs, ha.ea hok], ha.store (n := 16) hok (by decide) fun hp => by cases hp⟩

theorem step_sound_xop {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {op : XOp}
    (ha : Agree τ s₁ s₂) (hs : step τ (.xop op) = some τ')
    (e₁ : exec (.xop op) s₁ = some s₁') (e₂ : exec (.xop op) s₂ = some s₂') :
    addrs (.xop op) s₁ = addrs (.xop op) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, Option.some.injEq] at hs
  subst hs
  simp only [exec, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  rw [XOp.exec_eq op s₁, XOp.exec_eq op s₂]
  exact ⟨rfl, ha.withXmm _ _⟩

theorem step_sound_vop {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {op : VOp}
    (ha : Agree τ s₁ s₂) (hs : step τ (.vop op) = some τ')
    (e₁ : exec (.vop op) s₁ = some s₁') (e₂ : exec (.vop op) s₂ = some s₂') :
    addrs (.vop op) s₁ = addrs (.vop op) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, Option.some.injEq] at hs
  subst hs
  simp only [exec, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  rw [VOp.exec_eq op s₁, VOp.exec_eq op s₂]
  exact ⟨rfl, ha.withVec _ _ _ _⟩

theorem step_sound_vmovdquLoad {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {len : VLen} {d : XReg} {m : MemOp}
    (ha : Agree τ s₁ s₂) (hs : step τ (.vmovdquLoad len d m) = some τ')
    (e₁ : exec (.vmovdquLoad len d m) s₁ = some s₁') (e₂ : exec (.vmovdquLoad len d m) s₂ = some s₂') :
    addrs (.vmovdquLoad len d m) s₁ = addrs (.vmovdquLoad len d m) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok; cases hs
  cases len <;> simp only [exec, Option.map_eq_some_iff] at e₁ e₂ <;>
    obtain ⟨v₁, -, rfl⟩ := e₁ <;> obtain ⟨v₂, -, rfl⟩ := e₂ <;>
    exact ⟨by simp [addrs, ha.ea hok], ha.withVec _ _ _ _⟩

theorem step_sound_vbroadcasti128 {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {d : XReg} {m : MemOp}
    (ha : Agree τ s₁ s₂) (hs : step τ (.vbroadcasti128 d m) = some τ')
    (e₁ : exec (.vbroadcasti128 d m) s₁ = some s₁') (e₂ : exec (.vbroadcasti128 d m) s₂ = some s₂') :
    addrs (.vbroadcasti128 d m) s₁ = addrs (.vbroadcasti128 d m) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok; cases hs
  simp only [exec, Option.map_eq_some_iff] at e₁ e₂
  obtain ⟨v₁, -, rfl⟩ := e₁; obtain ⟨v₂, -, rfl⟩ := e₂
  exact ⟨by simp [addrs, ha.ea hok], ha.withVec _ _ _ _⟩

theorem step_sound_vmovdquStore {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {len : VLen} {m : MemOp} {r : XReg}
    (ha : Agree τ s₁ s₂) (hs : step τ (.vmovdquStore len m r) = some τ')
    (e₁ : exec (.vmovdquStore len m r) s₁ = some s₁') (e₂ : exec (.vmovdquStore len m r) s₂ = some s₂') :
    addrs (.vmovdquStore len m r) s₁ = addrs (.vmovdquStore len m r) s₂ ∧ Agree τ' s₁' s₂' := by
  cases len
  · simp only [step, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, State.store128] at e₁ e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ⟨by simp [addrs, ha.ea hok], ha.store (n := 16) hok (by decide) fun hp => by cases hp⟩
  · simp only [step, storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    simp only [exec, State.store256] at e₁ e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ⟨by simp [addrs, ha.ea hok], ha.store (n := 32) hok (by decide) fun hp => by cases hp⟩

theorem step_sound_stmxcsr {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {m : MemOp}
    (ha : Agree τ s₁ s₂) (hs : step τ (.stmxcsr m) = some τ')
    (e₁ : exec (.stmxcsr m) s₁ = some s₁') (e₂ : exec (.stmxcsr m) s₂ = some s₂') :
    addrs (.stmxcsr m) s₁ = addrs (.stmxcsr m) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, storeStep] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok; cases hs
  simp only [exec, State.store32] at e₁ e₂
  split at e₁ <;> [cases e₁; cases e₁]
  split at e₂ <;> [cases e₂; cases e₂]
  exact ⟨by simp [addrs, ha.ea hok], ha.store (n := 4) hok (by decide) fun hp => by cases hp⟩

theorem step_sound_ldmxcsr {τ τ' : T} {s₁ s₂ s₁' s₂' : State} {m : MemOp}
    (ha : Agree τ s₁ s₂) (hs : step τ (.ldmxcsr m) = some τ')
    (e₁ : exec (.ldmxcsr m) s₁ = some s₁') (e₂ : exec (.ldmxcsr m) s₂ = some s₂') :
    addrs (.ldmxcsr m) s₁ = addrs (.ldmxcsr m) s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step] at hs
  split at hs <;> [skip; cases hs]
  rename_i hok; cases hs
  simp only [exec, Option.bind_eq_some_iff] at e₁ e₂
  obtain ⟨v₁, -, e₁⟩ := e₁; obtain ⟨v₂, -, e₂⟩ := e₂
  split at e₁ <;> [cases e₁; cases e₁]
  split at e₂ <;> [cases e₂; cases e₂]
  exact ⟨by simp [addrs, ha.ea hok], ha.withMxcsr _ _⟩

theorem step_sound_lfence {τ τ' : T} {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (hs : step τ .lfence = some τ')
    (e₁ : exec .lfence s₁ = some s₁') (e₂ : exec .lfence s₂ = some s₂') :
    addrs .lfence s₁ = addrs .lfence s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [step, Option.some.injEq] at hs
  subst hs
  simp only [exec, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  exact ⟨rfl, ha⟩

end VG.X86_64.Taint
