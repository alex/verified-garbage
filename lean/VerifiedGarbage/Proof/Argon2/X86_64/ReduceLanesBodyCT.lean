import VerifiedGarbage.Proof.Argon2.X86_64.ReduceLanesBody
import VerifiedGarbage.Proof.Argon2.X86_64.ReduceLaneCT

/-! Reduction visits the same last blocks even when their contents differ. -/

namespace VG.Proof.Argon2.X86_64.ReduceLanes

open VG VG.X86_64 VG.Spec.Argon2 ReductionState

structure Related (p : Params) (lane : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block)
    (s t : State) : Prop where
  left : Ready p lane s
  right : Ready p lane t
  bases : s.gpr .rbp = t.gpr .rbp
  matrices : matrix s = matrix t
  leftRep : ReductionState.Represents p leftMemory leftAcc s
  rightRep : ReductionState.Represents p rightMemory rightAcc t

theorem advance_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block Impl.Argon2.X86_64.ReduceLanes.advance) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

theorem body_rel (p : Params) (lane : Nat) (leftMemory rightMemory : Array Block) (leftAcc rightAcc : Block) :
    RelCT isa (Related p lane leftMemory rightMemory leftAcc rightAcc) Impl.Argon2.X86_64.ReduceLanes.body
      (fun s t => s.cf = t.cf ∧ (lane + 1 < p.lanes → Related p (lane + 1) leftMemory rightMemory
        (xorBlock leftAcc (leftMemory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock))
        (xorBlock rightAcc (rightMemory[Proof.Argon2.lastIndex p lane]?.getD zeroBlock)) s t)) := by
  intro s t ts tt a b hp ea eb
  have related : ReduceLane.Related p lane s t :=
    ⟨hp.left.allocation, hp.right.allocation, hp.left.active, hp.left.laneWord, hp.right.laneWord, hp.bases, hp.matrices⟩
  cases ea with
  | seq reduceA advanceA =>
    cases eb with
    | seq reduceB advanceB =>
      obtain ⟨reduceTrace, _⟩ := ReduceLane.code_rel p lane _ _ _ _ _ _ related reduceA reduceB
      obtain ⟨_, sa, runA, reducedA⟩ := ReduceLane.code_ok s p lane hp.left.allocation hp.left.active
        hp.left.laneWord leftMemory leftAcc hp.leftRep
      obtain ⟨_, sb, runB, reducedB⟩ := ReduceLane.code_ok t p lane hp.right.allocation hp.right.active
        hp.right.laneWord rightMemory rightAcc hp.rightRep
      obtain ⟨_, rfl⟩ := Exec.det reduceA runA
      obtain ⟨_, rfl⟩ := Exec.det reduceB runB
      have bases := (reducedA.regs .rbp (by simp [calleeSaved])).trans
        (hp.bases.trans (reducedB.regs .rbp (by simp [calleeSaved])).symm)
      obtain ⟨advanceTrace, _⟩ := advance_rel _ _ _ _ _ _ bases advanceA advanceB
      obtain ⟨_, a', runA, doneA⟩ := body_ok s p lane hp.left leftMemory leftAcc hp.leftRep
      obtain ⟨_, b', runB, doneB⟩ := body_ok t p lane hp.right rightMemory rightAcc hp.rightRep
      obtain ⟨_, rfl⟩ := Exec.det (.seq reduceA advanceA) runA
      obtain ⟨_, rfl⟩ := Exec.det (.seq reduceB advanceB) runB
      refine ⟨by rw [reduceTrace, advanceTrace], doneA.cf.trans doneB.cf.symm, ?_⟩
      intro active
      refine ⟨doneA.next active, doneB.next active, ?_,
        doneA.base.trans (hp.matrices.trans doneB.base.symm), doneA.represented, doneB.represented⟩
      exact (doneA.regs .rbp (by simp [calleeSaved]) (by decide)).trans
        (hp.bases.trans (doneB.regs .rbp (by simp [calleeSaved]) (by decide)).symm)

end VG.Proof.Argon2.X86_64.ReduceLanes
