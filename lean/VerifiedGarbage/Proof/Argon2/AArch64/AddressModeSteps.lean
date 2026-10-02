import VerifiedGarbage.Impl.Argon2.AArch64.AddressMode
import VerifiedGarbage.Proof.Argon2.AArch64.Memory
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Argon2.AArch64.Carry

/-! Short mask computations for the public addressing-mode predicate. -/

namespace VG.Proof.Argon2.AArch64.AddressMode

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressMode
open VG.Impl.Argon2.AArch64

theorem zero_nat (x : Addr) : x.toNat < 1 ↔ x = 0#64 := by
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (Nat.lt_one_iff.mp h)
  · intro h; rw [h]; decide

theorem xor_nat (x y : Addr) : (x ^^^ y).toNat < 1 ↔ x = y := by
  rw [zero_nat, BitVec.xor_eq_zero_iff]

theorem borrow_lt (a b : Nat) :
    (if decide (b ≤ a) = true then (0 : Addr) else -1) =
      Divide.mask (decide (a < b)) := by
  by_cases h : a < b
  · simp only [show ¬b ≤ a by omega, decide_false, Bool.false_eq_true,
      ite_false, h, decide_true, Divide.mask, ite_true]
  · simp only [show b ≤ a by omega, decide_true, ite_true,
      h, decide_false, Divide.mask, Bool.false_eq_true, ite_false]

theorem kind_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 112) 8) :
    WP isa (.block kind) s fun t =>
      t.gpr .x6 = Divide.mask (decide (s.mem.readW (off (s.gpr .x19) 112) 64 = 1)) ∧
      t.gpr .x4 = Divide.mask (decide (s.mem.readW (off (s.gpr .x19) 112) 64 = 2)) ∧
      Divide.Keeps [.x8, .x6, .x4, .x12, .x13, .x14, .x15] s t := by
  simp only [off] at hr
  apply WP.of_runBlock
  simp only [kind, off, show 112 % 8 = 0 ∧ 112 < 4096 * 8 from by decide, hr, and_self,
    show (1#64).toNat = 1 from rfl, Instructions.mov, Instructions.load, Instructions.logici, Instructions.logic,
    Instructions.comparei, Instructions.compare, Instructions.sbb, Instructions.imm, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.read, Size.bytes, Size.bits,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_write, RegUpd.c_addWithCarry,


    BitVec.setWidth_eq, Bool.toNat_true, sub_value, sub_carry, borrow_mask, borrow_lt,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (1#16).setWidth 64 = 1#64 from rfl,
    show (2#16).setWidth 64 = 2#64 from rfl,
    show 1 < 65536 from by decide, show 2 < 65536 from by decide,
    show 0 < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    borrow_lt,  zero_nat, BitVec.xor_eq_zero_iff,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]
  all_goals rfl

theorem pass_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 0) 8) :
    WP isa (.block pass) s fun t =>
      t.gpr .x5 = Divide.mask (decide (s.mem.readW (off (s.gpr .x19) 0) 64 = 0#64)) ∧
      Divide.Keeps [.x5, .x13, .x14, .x15] s t := by
  simp only [off, BitVec.add_zero] at hr
  apply WP.of_runBlock
  simp only [pass, off, show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide, hr, and_self,
    show (1#64).toNat = 1 from rfl, Instructions.mov, Instructions.load,
    Instructions.comparei, Instructions.compare, Instructions.sbb, Instructions.imm, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.read, Size.bytes, Size.bits,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_write, RegUpd.c_addWithCarry,


    BitVec.setWidth_eq, Bool.toNat_true, sub_value, sub_carry, borrow_mask, borrow_lt,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (1#16).setWidth 64 = 1#64 from rfl,

    show 1 < 65536 from by decide,
    show 0 < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    borrow_lt,  zero_nat,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem slice_ok (s : State) : WP isa (.block slice) s fun t =>
    t.gpr .x6 = (s.gpr .x6 ||| ((s.gpr .x4 &&& s.gpr .x5) &&&
      Divide.mask (decide ((s.gpr .x22).toNat < 2)))) &&& 1 ∧
    Divide.Keeps [.x4, .x7, .x6, .x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [slice,  show (2#64).toNat = 2 from rfl, Instructions.mov,  Instructions.logici, Instructions.logic,
    Instructions.comparei, Instructions.compare, Instructions.sbb, Instructions.imm, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec,   State.read,  Size.bits,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_write, RegUpd.c_addWithCarry,


    BitVec.setWidth_eq, Bool.toNat_true, sub_value, sub_carry, borrow_mask, borrow_lt,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    show (1#16).setWidth 64 = 1#64 from rfl,
    show (2#16).setWidth 64 = 2#64 from rfl,
    show 1 < 65536 from by decide, show 2 < 65536 from by decide,
    show 0 < 4096 from by decide, show (63 : Nat) < 64 from by decide,
    BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    borrow_lt,
      Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.AArch64.AddressMode
