import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Body
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant-time CBC steps with public registers restored by the block call -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm VG.Impl.Rc2.Arm

def EqKept (s₁ s₂ : State) : Prop := ∀ r ∈ kept, s₁.gpr r = s₂.gpr r

def StepRel (s₁ s₂ : State) : Prop := StepPre s₁ ∧ StepPre s₂ ∧ EqKept s₁ s₂

theorem agreeKept {s₁ s₂ : State} (h : EqKept s₁ s₂) :
    VG.Arm.Taint.Agree (Taint.ofRegs kept) s₁ s₂ := Taint.agree_ofRegs h

theorem before_ok (d : Spec.Rc2.Direction) (s : State) (hp : StepPre s) :
    WP isa (.block (Impl.Rc2.Arm.Cbc.before d)) s (fun s' => StepPre s' ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r) := by
  have sep : ∀ r ∈ kept, r ∉ temps := by decide
  cases d
  · apply WP.mono (xor64_ok s .r1 .r4 (by decide) (by decide)
      (by simpa using hp.dataFit) hp.ivFit hp.readData hp.readIv hp.writeData)
    intro s' h
    exact ⟨hp.keep h, fun r hr => h.reg r (sep r hr)⟩
  · apply WP.mono (copy64_ok s .r1 .r2 0 256 (by decide) (by decide)
      (by simpa using hp.dataFit) (by have := hp.bufFit; omega)
      (by simpa using hp.readData) (hp.writeBuf 256 (by decide)))
    intro s' h
    exact ⟨hp.keep h, fun r hr => h.reg r (sep r hr)⟩

theorem kept_ct {c : Prog isa} (h : RelCT isa StepRel c (fun _ _ => True))
    (correct : ∀ s, StepPre s → WP isa c s (fun s' => StepPre s' ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r)) :
    RelCT isa StepRel c StepRel := by
  apply (h.wpDep (fun s₁ s₂ hp => ⟨correct s₁ hp.1, correct s₂ hp.2.1⟩)).mono
    (fun _ _ h => h)
  rintro s₁' s₂' ⟨_, s₁, s₂, hp, h₁, h₂⟩
  refine ⟨h₁.1, h₂.1, fun r hr => ?_⟩
  rw [h₁.2 r hr, h₂.2 r hr]
  exact hp.2.2 r hr

theorem before_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (.block (Impl.Rc2.Arm.Cbc.before d)) StepRel := by
  apply kept_ct _ (before_ok d)
  cases d <;> apply RelCT.taint (A := taint) (Taint.ofRegs kept) (fun _ _ h => agreeKept h.2.2)
  all_goals taint_decide

theorem call_ct (d : Spec.Rc2.Direction) : RelCT isa StepRel (Impl.Rc2.Arm.Cbc.blockCall d) StepRel := by
  apply kept_ct
  · cases d <;> apply RelCT.taint (A := taint) (Taint.ofRegs kept) (fun _ _ h => agreeKept h.2.2)
    all_goals taint_decide
  · intro s hp
    apply WP.mono (call_ok d s hp.call)
    intro s' h
    exact ⟨hp.transport h.rd h.wr h.reg, h.reg⟩

theorem after_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (.block (Impl.Rc2.Arm.Cbc.after d)) (fun _ _ => True) := by
  cases d <;> apply RelCT.taint (A := taint) (Taint.ofRegs kept) (fun _ _ h => agreeKept h.2.2)
  all_goals taint_decide

theorem step_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (Impl.Rc2.Arm.Cbc.step d) StepRel := by
  apply kept_ct ((before_ct d).seq ((call_ct d).seq (after_ct d)))
  intro s hp
  apply WP.mono (step_ok d s hp)
  intro s' h
  exact ⟨h.toPinned.pre hp, h.reg⟩

theorem body_ct (d : Spec.Rc2.Direction) :
    RelCT isa StepRel (Impl.Rc2.Arm.Cbc.body d) (fun _ _ => True) := by
  apply (step_ct d).seq
  apply RelCT.taint (A := taint) (Taint.ofRegs kept) (fun _ _ h => agreeKept h.2.2)
  taint_decide

end VG.Proof.Rc2.Arm.Cbc
