import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Call

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86 VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep)

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.TripleDes.X86.Ecb.advance s = some s' ∧
      s'.gpr .esi = s.gpr .esi + 8 ∧ s'.gpr .edi = s.gpr .edi - 1 ∧
      isa.eval .ne s' = some (!(s.gpr .edi - 1 == 0)) ∧ Keep [.esi, .edi] s s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.X86.Ecb.advance, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags,
      reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
  · rfl
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]

theorem counter_branch (x : BitVec 32) (hlo : 0 < x.toNat) :
    ((x - 1) != (0 : BitVec 32)) = decide (1 < x.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, decide_eq_true_eq]
  bv_omega_using [hlo]

end VG.Proof.TripleDes.X86.Ecb
