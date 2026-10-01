import VerifiedGarbage.Proof.Rc2.Arm.Cbc.StepCT
import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Loop

/-! # Constant-time CBC loops -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

def LoopRel (n : Nat) (s₁ s₂ : State) : Prop :=
  StepPre s₁ n ∧ StepPre s₂ n ∧ EqKept s₁ s₂ ∧
    s₁.gpr .r5 = BitVec.ofNat 32 n ∧ s₂.gpr .r5 = BitVec.ofNat 32 n ∧ 1 ≤ n

theorem bodyRel (d : Spec.Rc2.Direction) (n : Nat) :
    RelCT isa (LoopRel n) (Impl.Rc2.Arm.Cbc.body d) (fun s₁ s₂ =>
      EqKept s₁ s₂ ∧ eval .ne s₁ = eval .ne s₂ ∧
        (eval .ne s₁ = some true → ∃ m < n, LoopRel m s₁ s₂)) := by
  have ct : RelCT isa (LoopRel n) (Impl.Rc2.Arm.Cbc.body d) (fun _ _ => True) :=
    (body_ct d).mono (fun _ _ h => ⟨h.1.head h.2.2.2.2.2, h.2.1.head h.2.2.2.2.2, h.2.2.1⟩)
      (fun _ _ _ => trivial)
  have correct (s₁ s₂ : State) (h : LoopRel n s₁ s₂) :=
    And.intro (body_ok d s₁ n h.2.2.2.2.2 (by have := h.1.dataFit; omega) h.2.2.2.1 (h.1.head h.2.2.2.2.2))
      (body_ok d s₂ n h.2.2.2.2.2 (by have := h.2.1.dataFit; omega) h.2.2.2.2.1 (h.2.1.head h.2.2.2.2.2))
  apply (ct.wpDep correct).mono (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  have eq : EqKept s₁' s₂' := by
    intro r hr
    by_cases hptr : r = .r1
    · subst r; rw [h₁.ptr, h₂.ptr, hp.2.2.1 .r1 (by decide)]
    · by_cases hcount : r = .r5
      · subst r; rw [h₁.count, h₂.count]
      · rw [h₁.reg r hr hptr hcount, h₂.reg r hr hptr hcount]
        exact hp.2.2.1 r hr
  refine ⟨eq, by rw [eval_nonzeroCount, eval_nonzeroCount, h₁.flag, h₂.flag], ?_⟩
  intro hcontinue
  have hn : 1 ≤ n := hp.2.2.2.2.2
  have hm : 1 ≤ n - 1 := by
    rw [eval_nonzeroCount, h₁.flag] at hcontinue
    by_contra h
    have e : n = 1 := by omega
    simp only [e, decide_true, Option.map_some, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at hcontinue
  refine ⟨n - 1, by omega, ?_, ?_, eq, h₁.count, h₂.count, hm⟩
  · have e : n = (n - 1) + 1 := by omega
    rw [e] at h₁ hp
    exact h₁.tail hp.1 hm
  · have e : n = (n - 1) + 1 := by omega
    rw [e] at h₂ hp
    exact h₂.tail hp.2.1 hm

theorem loop_ct (d : Spec.Rc2.Direction) (n : Nat) :
    RelCT isa (LoopRel n) (.loop (Impl.Rc2.Arm.Cbc.body d) .ne) EqKept := by
  refine RelCT.loop (M := isa) (body := Impl.Rc2.Arm.Cbc.body d) (c := .ne) (Q := EqKept) LoopRel ?_ n
  intro m
  exact (bodyRel d m).mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, fun _ => h.1, h.2.2⟩)

def MaybeRel (s₁ s₂ : State) : Prop :=
  ∃ n, StepPre s₁ n ∧ StepPre s₂ n ∧ EqKept s₁ s₂ ∧
    s₁.gpr .r5 = BitVec.ofNat 32 n ∧ s₂.gpr .r5 = BitVec.ofNat 32 n ∧
    zeroCount s₁ = some (decide (n = 0)) ∧ zeroCount s₂ = some (decide (n = 0))

theorem maybeLoop_ct (d : Spec.Rc2.Direction) :
    RelCT isa MaybeRel (.ite .eq (.block []) (.loop (Impl.Rc2.Arm.Cbc.body d) .ne)) EqKept := by
  apply RelCT.ite
  · rintro s₁ s₂ ⟨n, _, _, _, _, _, h₁, h₂⟩
    change zeroCount s₁ = zeroCount s₂
    rw [h₁, h₂]
  · apply RelCT.block_nil
    rintro s₁ s₂ ⟨⟨n, _, _, eq, _⟩, _⟩
    exact eq
  · apply RelCT.exists_ (fun n => loop_ct d n) |>.mono
    · rintro s₁ s₂ ⟨⟨n, h₁, h₂, eq, c₁, c₂, z₁, _⟩, branch⟩
      refine ⟨n, h₁, h₂, eq, c₁, c₂, ?_⟩
      change zeroCount s₁ = some false at branch
      rw [z₁] at branch
      have hn : n ≠ 0 := by intro hz; simp [hz] at branch
      omega
    · exact fun _ _ h => h

end VG.Proof.Rc2.Arm.Cbc
