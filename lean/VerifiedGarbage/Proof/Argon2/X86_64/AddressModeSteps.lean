import VerifiedGarbage.Impl.Argon2.X86_64.AddressMode
import VerifiedGarbage.Proof.Argon2.X86_64.Memory
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep

/-! Short mask computations for the public addressing-mode predicate. -/

namespace VG.Proof.Argon2.X86_64.AddressMode

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressMode

theorem zero_nat (x : Addr) : x.toNat < 1 ↔ x = 0#64 := by
  constructor
  · intro h; exact BitVec.eq_of_toNat_eq (Nat.lt_one_iff.mp h)
  · intro h; rw [h]; decide

theorem xor_nat (x y : Addr) : (x ^^^ y).toNat < 1 ↔ x = y := by
  rw [zero_nat, BitVec.xor_eq_zero_iff]

theorem kind_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 112) 8) :
    WP isa (.block kind) s fun t =>
      t.gpr .r10 = Divide.mask (decide (s.mem.readW (off (s.gpr .rbp) 112) 64 = 1)) ∧
      t.gpr .r8 = Divide.mask (decide (s.mem.readW (off (s.gpr .rbp) 112) 64 = 2)) ∧
      Divide.Keeps [.rax, .r10, .r8] s t := by
  apply WP.of_runBlock
  simp only [kind, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, reduceCtorEq, ite_true, ite_false,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show BitVec.signExtend 64 (2 : BitVec 32) = (2 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', Divide.sbb_mask, show (1 : Addr).toNat = 1 from rfl, xor_nat]
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem pass_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa (.block pass) s fun t =>
      t.gpr .r9 = Divide.mask (decide (s.mem.readW (off (s.gpr .rbp) 0) 64 = 0#64)) ∧
      Divide.Keeps [.r9] s t := by
  apply WP.of_runBlock
  simp only [pass, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hr, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.cf_arithFlags, ite_true,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', Divide.sbb_mask, show (1 : Addr).toNat = 1 from rfl, zero_nat]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem slice_ok (s : State) : WP isa (.block slice) s fun t =>
    t.gpr .r10 = (s.gpr .r10 ||| ((s.gpr .r8 &&& s.gpr .r9) &&&
      Divide.mask (decide ((s.gpr .r14).toNat < 2)))) &&& 1 ∧
    Divide.Keeps [.r8, .r11, .r10] s t := by
  apply WP.of_runBlock
  simp only [slice, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    reduceCtorEq, ite_true, ite_false,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show BitVec.signExtend 64 (2 : BitVec 32) = (2 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', Divide.sbb_mask, show (2 : Addr).toNat = 2 from rfl]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.AddressMode
