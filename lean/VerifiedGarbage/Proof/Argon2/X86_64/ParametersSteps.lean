import VerifiedGarbage.Impl.Argon2.X86_64.Parameters
import VerifiedGarbage.Proof.Argon2.X86_64.Divide
import VerifiedGarbage.Proof.Argon2.X86_64.DivideCT
import VerifiedGarbage.Proof.Argon2.X86_64.Initialize
import VerifiedGarbage.Proof.Argon2.Dimensions

/-! Public frame loads and fixed arithmetic for the RFC's rounded memory dimensions. -/

namespace VG.Proof.Argon2.X86_64.Parameters

open VG VG.X86_64

theorem args_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 176) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 184) 8) :
    WP isa (.block Impl.Argon2.X86_64.Parameters.args) s fun t =>
      t.gpr .rdi = s.mem.readW (off (s.gpr .rbp) 176) 64 ∧
      t.gpr .rsi = (s.mem.readW (off (s.gpr .rbp) 184) 64) * 4 ∧ Divide.Keeps [.rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.Parameters.args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, State.load64, ea_at, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, memoryRead, lanesRead, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ?_⟩
  · simp only [show (4 : Addr) = 2#64 + 2#64 from rfl, BitVec.mul_add, BitVec.mul_two]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
    all_goals rfl

theorem finish_ok (s : State) : WP isa (.block Impl.Argon2.X86_64.Parameters.finish) s fun t =>
    t.gpr .r13 = s.gpr .r9 * 4 ∧ Divide.Keeps [.r13] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.Parameters.finish, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · simp only [show (4 : Addr) = 2#64 + 2#64 from rfl, BitVec.mul_add, BitVec.mul_two]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
    all_goals rfl

end VG.Proof.Argon2.X86_64.Parameters
