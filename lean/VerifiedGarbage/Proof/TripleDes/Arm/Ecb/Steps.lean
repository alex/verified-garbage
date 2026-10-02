import VerifiedGarbage.Proof.TripleDes.Arm.Ecb.Call
import VerifiedGarbage.Proof.TripleDes.EcbMemory
import VerifiedGarbage.Proof.Rc2.Arm.KeySteps

namespace VG.Proof.TripleDes.Arm.Ecb
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (Keep gpr_subFlags mem_subFlags rd_subFlags wr_subFlags)

def zeroCount (s : State) : Option Bool := some s.z

theorem eval_zeroCount (s : State) : eval .eq s = zeroCount s := rfl
theorem eval_nonzeroCount (s : State) : eval .ne s = (zeroCount s).map (! ·) := rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.TripleDes.Arm.Ecb.advance s = some s' ∧
      s'.gpr .r1 = s.gpr .r1 + 8 ∧ s'.gpr .r3 = s.gpr .r3 - 1 ∧
      zeroCount s' = some ((s.gpr .r3 - 1) == 0) ∧ Keep [.r1, .r3] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [Impl.TripleDes.Arm.Ecb.advance,
      runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, ite_true, Option.map_some,
      gpr_setReg, ite_false]
    rfl, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · rfl
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_subFlags, gpr_setReg, hr.1, hr.2, ite_false]
    · simp only [mem_subFlags, mem_setReg]
    · simp only [rd_subFlags, rd_setReg]
    · simp only [wr_subFlags, wr_setReg]

theorem counter_zero (n : Nat) (hn : n < 2 ^ 32) :
    ((BitVec.ofNat 32 n) == (0 : BitVec 32)) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at ht
    exact ht
  · intro h; rw [h]; rfl

end VG.Proof.TripleDes.Arm.Ecb
