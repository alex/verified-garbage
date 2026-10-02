import VerifiedGarbage.Impl.Argon2.AArch64.ReducePointers
import VerifiedGarbage.Proof.Argon2.AArch64.BlockAddress
import VerifiedGarbage.Proof.Argon2.AArch64.FillIterations
import VerifiedGarbage.Proof.Argon2.FinalReduction

/-! The last-lane address calculation preserves all callee-saved registers. -/

namespace VG.Proof.Argon2.AArch64.ReducePointers

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.ReducePointers

def changed : List Reg := [.x4, .x8, .x3, .x2, .x1, .x0, .x12, .x15]

theorem setup_ok (s : State) (read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 232) 8) :
    WP isa (.block Impl.Argon2.AArch64.ReducePointers.setup) s fun t =>
      t.gpr .x4 = s.mem.readW (off (s.gpr .x19) 232) 64 ∧
      t.gpr .x8 = s.gpr .x24 ∧ t.gpr .x3 = s.gpr .x20 - 1 ∧
      Divide.Keeps [.x4, .x8, .x3, .x12, .x15] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.ReducePointers.setup,
    Impl.Argon2.AArch64.Instructions.load, Impl.Argon2.AArch64.Instructions.mov,
    Impl.Argon2.AArch64.Instructions.subi, Impl.Argon2.AArch64.Instructions.sub,
    Impl.Argon2.AArch64.Instructions.imm, Impl.Argon2.AArch64.Instructions.mark,
    show 1 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, State.load, addr, Size.bytes, Size.bits,
    show 232 % 8 = 0 ∧ 232 < 4096 * 8 from by decide,
    show 0 < 4096 from by decide, Nat.reduceMul, Nat.reduceLT, and_self,
    read, BitVec.shiftLeft_zero, show (1#16).setWidth 64 = 1#64 from rfl,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, BitVec.setWidth_eq, BitVec.add_zero,
    Bool.toNat_true, sub_value, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, trivial, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]
  all_goals rfl

theorem finish_ok (s : State) : WP isa (.block Impl.Argon2.AArch64.ReducePointers.finish) s fun t =>
    t.gpr .x1 = s.gpr .x8 ∧ t.gpr .x0 = s.gpr .x4 ∧ Divide.Keeps [.x1, .x0] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.ReducePointers.finish, Impl.Argon2.AArch64.Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 0 < 4096 from by decide, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem code_ok (s : State) (lane q : Nat) (positive : 0 < q)
    (read : InRegions (s.rd ++ s.wr) (off (s.gpr .x19) 232) 8)
    (laneWord : s.gpr .x24 = BitVec.ofNat 64 lane) (lengthWord : s.gpr .x20 = BitVec.ofNat 64 q) :
    WP isa code s fun t =>
      t.gpr .x0 = s.mem.readW (off (s.gpr .x19) 232) 64 ∧
      t.gpr .x1 = Proof.Argon2.matrixCell (s.mem.readW (off (s.gpr .x19) 232) 64) ((lane + 1) * q - 1) ∧
      Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((setup_ok s read).mono ?_)
  rintro a ⟨base, lan, col, ka⟩
  have column : a.gpr .x3 = BitVec.ofNat 64 (q - 1) := by
    rw [col, lengthWord]
    exact Offset.ofNat_sub_ofNat (by omega : 1 ≤ q)
  refine WP.seq ((BlockAddress.code_nat_ok a lane (q - 1) q (lan.trans laneWord) column
    ((ka.regs .x20 (by decide)).trans lengthWord)).mono ?_)
  rintro b ⟨address, kb⟩
  refine (finish_ok b).mono ?_
  rintro t ⟨src, dest, kt⟩
  refine ⟨dest.trans ((kb.regs .x4 (by decide)).trans base), ?_, ?_⟩
  · rw [src, address, base]
    unfold Proof.Argon2.matrixCell
    have offset : lane * q + (q - 1) = (lane + 1) * q - 1 := by rw [Nat.add_mul, Nat.one_mul]; omega
    rw [offset]
  · exact (ka.mono (by simp [changed])).trans
      ((kb.mono (by simp [changed])).trans (kt.mono (by simp [changed])))

end VG.Proof.Argon2.AArch64.ReducePointers
