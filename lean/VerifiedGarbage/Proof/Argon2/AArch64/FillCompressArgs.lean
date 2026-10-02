import VerifiedGarbage.Impl.Argon2.AArch64.FillCompress
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Argon2.AArch64.Memory

/-! Save the current cell across G and reload the block-write arguments. -/
namespace VG.Proof.Argon2.AArch64.FillCompress
open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillCompress
open VG.Impl.Argon2.AArch64

theorem saveCurrent_ok (s : State)
    (hw : InRegions s.wr (off (s.gpr .x19) 16) 8) :
    WP isa (.block saveCurrent) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x19) 16) (s.gpr .x6) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [saveCurrent, Instructions.store, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, State.store, State.read, Size.bytes, and_self, Option.bind_some, Size.bits, BitVec.setWidth_eq, hw,
    show 16 % 8 = 0 ∧ 16 < 4096 * 8 from by decide,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial⟩

theorem compressArgs_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block compressArgs) s fun t =>
      t.gpr .x3 = s.mem.readW (off (s.gpr .x19) 248) 64 ∧
      t.gpr .x2 = s.mem.readW (off (s.gpr .x19) 248) 64 + 4096 ∧ Divide.Keeps [.x3, .x2, .x12, .x15] s t := by
  simp only [off] at hr
  apply WP.of_runBlock
  simp only [compressArgs, Instructions.load, Instructions.mov, Instructions.addi,
    Instructions.imm, Instructions.mark, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, off, and_self, Option.map_some, Option.bind_some,
    State.read, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    hr,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide,
    show ¬4096 < 4096 from by decide,
    show 4096 < 65536 from by decide,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem writeArgs_ok (s : State)
    (destRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 16) 8)
    (workRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa (.block writeArgs) s fun t =>
      t.gpr .x0 = s.mem.readW (off (s.gpr .x19) 16) 64 ∧
      t.gpr .x1 = s.mem.readW (off (s.gpr .x19) 248) 64 + 4096 ∧
      t.gpr .x5 = s.mem.readW (off (s.gpr .x19) 0) 64 ∧ Divide.Keeps [.x0, .x1, .x5, .x12, .x15] s t := by
  simp only [off, BitVec.add_zero] at destRead workRead passRead
  apply WP.of_runBlock
  simp only [writeArgs, Instructions.load, Instructions.mov, Instructions.addi,
    Instructions.imm, Instructions.mark, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, off, and_self, Option.map_some, Option.bind_some,
    State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, Size.bits, BitVec.setWidth_eq,
    show 16 % 8 = 0 ∧ 16 < 4096 * 8 from by decide,
    show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide, BitVec.add_zero,
    destRead, workRead, passRead,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide,
    show ¬4096 < 4096 from by decide,
    show 4096 < 65536 from by decide,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.AArch64.FillCompress
