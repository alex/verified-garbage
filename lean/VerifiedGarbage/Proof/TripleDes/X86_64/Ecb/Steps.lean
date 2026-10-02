import VerifiedGarbage.Proof.TripleDes.X86_64.Ecb.Call

namespace VG.Proof.TripleDes.X86_64.Ecb

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Rc2.X86_64 (Keep)

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.TripleDes.X86_64.Ecb.advance s = some s' ∧
      s'.gpr .rsi = s.gpr .rsi + 8 ∧ s'.gpr .rbp = s.gpr .rbp - 1 ∧
      s'.zf = some ((s.gpr .rbp - 1) == 0) ∧ Keep [.rsi, .rbp] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [Impl.TripleDes.X86_64.Ecb.advance,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, gpr_setReg, gpr_arithFlags, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    rfl
  · exact gpr_setReg_self _ _ _
  · rw [zf_setReg, zf_arithFlags]
    rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

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

end VG.Proof.TripleDes.X86_64.Ecb
