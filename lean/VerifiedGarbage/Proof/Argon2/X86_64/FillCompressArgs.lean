import VerifiedGarbage.Impl.Argon2.X86_64.FillCompress
import VerifiedGarbage.Proof.Argon2.X86_64.Memory
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep

/-! Save the current cell across G and reload the block-write arguments. -/

namespace VG.Proof.Argon2.X86_64.FillCompress

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillCompress

theorem saveCurrent_ok (s : State)
    (hw : InRegions s.wr (off (s.gpr .rbp) 16) 8) :
    WP isa (.block saveCurrent) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rbp) 16) (s.gpr .r10) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [saveCurrent, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.store64, ea_at, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem compressArgs_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8) :
    WP isa (.block compressArgs) s fun t =>
      t.gpr .rcx = s.mem.readW (off (s.gpr .rbp) 248) 64 ∧
      t.gpr .rdx = s.mem.readW (off (s.gpr .rbp) 248) 64 + 4096 ∧
      Divide.Keeps [.rcx, .rdx] s t := by
  apply WP.of_runBlock
  simp only [compressArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, State.load64, ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (4096 : BitVec 32) = (4096 : Addr) from rfl]
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
  all_goals rfl

theorem writeArgs_ok (s : State)
    (destRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 16) 8)
    (workRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa (.block writeArgs) s fun t =>
      t.gpr .rdi = s.mem.readW (off (s.gpr .rbp) 16) 64 ∧
      t.gpr .rsi = s.mem.readW (off (s.gpr .rbp) 248) 64 + 4096 ∧
      t.gpr .r9 = s.mem.readW (off (s.gpr .rbp) 0) 64 ∧
      Divide.Keeps [.rdi, .rsi, .r9] s t := by
  apply WP.of_runBlock
  simp only [writeArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, State.load64, ea_at, destRead, workRead, passRead, execAlu,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    show BitVec.signExtend 64 (4096 : BitVec 32) = (4096 : Addr) from rfl]
  refine ⟨trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.FillCompress
