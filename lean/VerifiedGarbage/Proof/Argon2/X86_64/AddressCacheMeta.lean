import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceStart
import VerifiedGarbage.Impl.Argon2.X86_64.AddressCache
import VerifiedGarbage.Proof.Argon2.X86_64.AddressCallsPrepare

/-! Public cache counters and indexed-word arguments. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCache

def counter (index : Addr) : Addr := (index >>> 7) + 1

theorem check_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 8) 8) :
    WP isa (.block check) s fun t => t.gpr .rax = counter (s.gpr .r15) ∧
      t.zf = decide (counter (s.gpr .r15) = s.mem.readW (off (s.gpr .rbp) 8) 64) ∧
      Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [check, counter, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, execAlu, State.load64, ea_at, hr, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_setFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.wr_arithFlags,
    RegUpd.zf_arithFlags, reduceCtorEq, ite_true, ite_false, and_self,
    show 1 ≤ (7 : Nat) ∧ (7 : Nat) ≤ 63 from by decide,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ?_⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, ReferenceStart.sub_zero_iff]
    exact ⟨fun h => decide_eq_true h, of_decide_eq_true⟩
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr, ite_false]
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
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8) :
    WP isa (.block wordArgs) s fun t => t.gpr .rcx = AddressCalls.work s ∧
      t.gpr .rax = s.gpr .r15 &&& 127 ∧ Divide.Keeps [.rcx, .rax] s t := by
  apply WP.of_runBlock
  simp only [wordArgs, AddressCalls.work, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, ea_at, hr, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_true, ite_false,
    show BitVec.signExtend 64 (127 : BitVec 32) = (127 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
  all_goals rfl

theorem index_nat (index : Addr) : index &&& 127 = BitVec.ofNat 64 (index.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.and_two_pow_sub_one_eq_mod index.toNat 7

end VG.Proof.Argon2.X86_64.AddressCache
