import VerifiedGarbage.Proof.Argon2.AArch64.ReferenceStart
import VerifiedGarbage.Proof.Argon2.AArch64.Carry
import VerifiedGarbage.Impl.Argon2.AArch64.AddressCache
import VerifiedGarbage.Proof.Argon2.AArch64.AddressCallsPrepare

/-! Public cache counters and indexed-word arguments. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCache
open VG.Impl.Argon2.AArch64

def counter (index : Addr) : Addr := (index >>> 7) + 1

theorem check_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 8) 8) :
    WP isa (.block check) s fun t => t.gpr .x8 = counter (s.gpr .x23) ∧
      t.gpr .x15 = counter (s.gpr .x23) - s.mem.readW (off (s.gpr .x19) 8) 64 ∧
      Divide.Keeps [.x8, .x13, .x14, .x15] s t := by
  simp only [off] at hr
  apply WP.of_runBlock
  simp only [check, counter, Instructions.mov, Instructions.shr, Instructions.mark,
    Instructions.addi, Instructions.comparem, Instructions.compare, Instructions.load,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, addr, State.load, Size.bytes, Size.bits,
    show 8 % 8 = 0 ∧ 8 < 4096 * 8 from by decide,
    show (7 : Nat) < 64 from by decide, show (63 : Nat) < 64 from by decide,
    show 0 < 4096 from by decide, show 1 < 4096 from by decide,
    hr, and_self, ite_true, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.gpr_addWithCarry,
    sub_value, Bool.toNat_true, BitVec.setWidth_eq,
    reduceCtorEq, ite_false, BitVec.add_zero,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem counter_nat (index : Addr) : counter index = BitVec.ofNat 64 (index.toNat / 128 + 1) := by
  have shifted : index >>> 7 = BitVec.ofNat 64 (index.toNat / 128) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := index.isLt; omega)]
  unfold counter
  rw [shifted]
  exact (BitVec.ofNat_add _ _).symm

theorem counter_ne_zero (index : Addr) : counter index ≠ 0 := by
  have bound : index.toNat / 128 + 1 < 2 ^ 64 := by have := index.isLt; omega
  intro h
  have nat := congrArg BitVec.toNat h
  rw [counter_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at nat
  change index.toNat / 128 + 1 = 0 at nat
  omega

theorem wordArgs_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 248) 8) :
    WP isa (.block wordArgs) s fun t => t.gpr .x3 = AddressCalls.work s ∧
      t.gpr .x8 = s.gpr .x23 &&& 127 ∧ Divide.Keeps [.x3, .x8, .x12, .x15] s t := by
  simp only [off] at hr
  apply WP.of_runBlock
  simp only [wordArgs, AddressCalls.work, off, Instructions.mov, Instructions.load,
    Instructions.logici, Instructions.logic, Instructions.imm, Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, addr, State.load, Size.bytes, Size.bits,
    show 248 % 8 = 0 ∧ 248 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide, show 127 < 65536 from by decide,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero, hr, and_self, ite_true,
    RegUpd.gpr_write,
    BitVec.setWidth_eq, reduceCtorEq, ite_false, BitVec.add_zero,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

theorem index_nat (index : Addr) : index &&& 127 = BitVec.ofNat 64 (index.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.and_two_pow_sub_one_eq_mod index.toNat 7

end VG.Proof.Argon2.AArch64.AddressCache
