import VerifiedGarbage.Proof.Argon2.AArch64.Parameters
import VerifiedGarbage.Proof.Argon2.AArch64.InitialBodyState

/-! Compute the rounded lane length before entering the complete Argon2 body. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64.Initial

/-- A specification state for the body's readiness predicate, not executable code. -/
def dimensionState (s : State) (p : Params) : State :=
  s.write .x .x21 (BitVec.ofNat 64 p.laneLen)

theorem dimension_frame (s : State) (p : Params) : InitialBody.SameFrame s (dimensionState s p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact RegUpd.gpr_write_of_ne s .x _ (by decide)
  · exact RegUpd.gpr_write_of_ne s .x _ (by decide)
  · rfl
  · exact RegUpd.mem_write ..
  · exact RegUpd.rd_write ..
  · exact RegUpd.wr_write ..

theorem parameters_frame {s t : State} (p : Params)
    (keeps : Divide.Keeps Parameters.changed s t) :
    InitialBody.SameFrame (dimensionState s p) t := by
  have frame := dimension_frame s p
  refine ⟨?_, ?_, ?_, keeps.mem.trans frame.mem.symm,
    keeps.rd.trans frame.rd.symm, keeps.wr.trans frame.wr.symm⟩
  · exact (keeps.regs .x19 (by decide)).trans frame.bp.symm
  · exact (keeps.regs .x24 (by decide)).trans frame.bx.symm
  · exact keeps.sp.trans frame.sp.symm

theorem parameters_ready {s t : State} {p : Params}
    (h : InitialBody.Ready p (dimensionState s p))
    (length : t.gpr .x21 = BitVec.ofNat 64 p.laneLen)
    (keeps : Divide.Keeps Parameters.changed s t) : InitialBody.Ready p t :=
  h.of_state (parameters_frame p keeps) length

theorem parameters_body_ok (v : HPrime.Backend) (name : String)
    (s : State) (p : Params) (parameters : Parameters.Ready p s)
    (body : InitialBody.Ready p (dimensionState s p)) :
    WP isa (.seq Impl.Argon2.AArch64.Parameters.code
      (Impl.Argon2.AArch64.InitialBody.code name v.hash)) s (InitialBody.Done s · p) := by
  refine WP.seq ((Parameters.code_ok s p parameters).mono ?_)
  rintro a ⟨length, keeps⟩
  refine (InitialBody.code_ok v name a p (parameters_ready body length keeps)).mono ?_
  intro t done
  have bp := keeps.regs .x19 (by decide)
  have sp := keeps.sp
  have base : FillKernel.matrix a = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : FinalOutput.work a = FinalOutput.work s := by
    unfold FinalOutput.work; rw [keeps.mem, bp]
  have output : FinalOutput.output a = FinalOutput.output s := by
    unfold FinalOutput.output; rw [keeps.mem, bp]
  refine ⟨?_, done.bp.trans bp, done.sp.trans sp,
    done.rd.trans keeps.rd, done.wr.trans keeps.wr, ?_, ?_⟩
  · have digest := done.digest
    simp only [Initial.inputBytes, Initial.wordAt, keeps.mem, bp, output] at digest
    exact digest
  · have frame := done.frame
    rw [InitFill.writes_eq s a p bp sp base work output] at frame
    rw [keeps.mem] at frame
    exact frame
  · intro r hr
    have facts : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], r ∉ Parameters.changed := by decide
    exact (done.unused r hr).trans (keeps.regs r (facts r hr))

end VG.Proof.Argon2.AArch64.Derive
