import VerifiedGarbage.Proof.TripleDes.AArch64.Ecb.Call
import VerifiedGarbage.Proof.TripleDes.EcbMemory

/-! # ECB pointer advancement and public loop counters -/

namespace VG.Proof.TripleDes.AArch64.Ecb

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Proof.Rc2.AArch64 (Keep)

def zeroCount (s : State) : Option Bool := some (s.gpr .x23 == 0)

theorem eval_zeroCount (s : State) : eval (.zero .x .x23) s = zeroCount s := rfl

theorem eval_nonzeroCount (s : State) : eval (.nonzero .x .x23) s = (zeroCount s).map (! ·) := rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.TripleDes.AArch64.Ecb.advance s = some s' ∧
      s'.gpr .x1 = s.gpr .x1 + 8 ∧ s'.gpr .x23 = s.gpr .x23 - 1 ∧
      zeroCount s' = some ((s.gpr .x23 - 1) == 0) ∧ Keep [.x1, .x23] s s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.AArch64.Ecb.advance, runBlock_cons, runStep_some, runBlock_nil,
      exec, State.read, BitVec.setWidth_eq, Nat.reduceLT, ite_true,
      gpr_write, reduceCtorEq, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    rfl
  · exact gpr_write_self _ _ _ _
  · rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, hr.1, hr.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

theorem counter_zero (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n) == (0 : BitVec 64)) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at ht
    exact ht
  · intro h
    rw [h]
    rfl

end VG.Proof.TripleDes.AArch64.Ecb
