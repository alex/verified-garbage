import VerifiedGarbage.Impl.Argon2.AArch64.Initial
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions

/-! Argument handling for the H₀ streaming hash. -/
namespace VG.Proof.Argon2.AArch64.Initial
open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial

theorem headerWord_ok (s : State) (source destination : Nat)
    (sourceAlign : source % 8 = 0) (sourceBound : source < 32768)
    (destinationAlign : destination % 4 = 0) (destinationBound : destination < 16384)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 source) 8)
    (hw : InRegions s.wr (s.gpr .x24 + BitVec.ofNat 64 destination) 4) :
    WP isa (.block (headerWord source destination)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .x24 + BitVec.ofNat 64 destination)
        ((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 source) 64).setWidth 32) ∧
      (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [headerWord, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.store32, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, State.load, State.store, addr, Size.bytes, Size.bits,
    sourceAlign, sourceBound, destinationAlign, destinationBound, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hr, hw, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, trivial, trivial, rfl⟩
  intro r hr
  simp only [hr, ite_false]

structure LengthArgs (s : State) (offset : Nat) (t : State) : Prop where
  length : t.gpr .x22 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 offset) 64
  count : t.gpr .x1 = s.gpr .x20
  pointer : t.gpr .x2 = s.gpr .x24 + 792
  size : t.gpr .x3 = 4
  other : ∀ r, r ∉ [Reg.x22, .x1, .x2, .x3, .x15] → t.gpr r = s.gpr r
  mem : t.mem = s.mem.writeW (s.gpr .x24 + 792)
    ((s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 offset) 64).setWidth 32)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem lengthArgs_ok (s : State) (offset : Nat)
    (aligned : offset % 8 = 0) (bound : offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 offset) 8)
    (hw : InRegions s.wr (s.gpr .x24 + 792) 4) :
    WP isa (.block (lengthArgs offset)) s (LengthArgs s offset) := by
  have hwLiteral : InRegions s.wr (s.gpr .x24 + 792#64) 4 := hw
  apply WP.of_runBlock
  simp only [lengthArgs, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.store32, Impl.Argon2.AArch64.Instructions.mov,
    Impl.Argon2.AArch64.Instructions.addi, Impl.Argon2.AArch64.Instructions.mark,
    Impl.Argon2.AArch64.Instructions.imm, show 4 < 65536 from by decide,
    show 792 < 4096 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, State.load, State.store, addr, Size.bytes, Size.bits,
    aligned, bound, show 792 % 4 = 0 ∧ 792 < 4096 * 4 from by decide, and_self,
    show 0 < 4096 from by decide, Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, show (4#16).setWidth 64 = 4#64 from rfl,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hr, hwLiteral, BitVec.setWidth_eq, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, ite_true]; rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  · simp only [RegUpd.mem_write]; rfl
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

structure InputArgs (s t : State) (offset : Nat) : Prop where
  total : t.gpr .x20 = s.gpr .x20 + 4
  count : t.gpr .x1 = s.gpr .x20 + 4
  pointer : t.gpr .x2 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 offset) 64
  length : t.gpr .x3 = s.gpr .x22
  other : ∀ r, r ∉ [Reg.x20, .x1, .x2, .x3, .x15] → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem inputArgs_ok (s : State) (offset : Nat)
    (aligned : offset % 8 = 0) (bound : offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (inputArgs offset)) s (fun t => InputArgs s t offset) := by
  apply WP.of_runBlock
  simp only [inputArgs, Impl.Argon2.AArch64.Instructions.addi,
    Impl.Argon2.AArch64.Instructions.mark, Impl.Argon2.AArch64.Instructions.mov,
    Impl.Argon2.AArch64.Instructions.load, show 4 < 4096 from by decide,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, State.load,
    addr, Size.bytes, Size.bits, aligned, bound, and_self,
    show 0 < 4096 from by decide, RegUpd.gpr_write,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hr,
    BitVec.setWidth_eq, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]
end VG.Proof.Argon2.AArch64.Initial
