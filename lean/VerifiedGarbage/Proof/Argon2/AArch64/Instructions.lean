import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Argon2.AArch64.Carry
import VerifiedGarbage.Impl.Argon2.AArch64.Instructions

/-! Short register operations used by the allocation and loop drivers. -/
namespace VG.Proof.Argon2.AArch64.Instructions
open VG VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

theorem addi_ok (s : State) (d : Reg) (n : Nat) (hn : n < 65536)
    (hd : d ≠ .x12) (h15 : d ≠ .x15) :
    WP isa (.block (addi d n)) s fun t =>
      t.gpr d = s.gpr d + BitVec.ofNat 64 n ∧ Divide.Keeps [d, .x12, .x15] s t := by
  have width : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
    exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) hn
  by_cases small : n < 4096
  · apply WP.of_runBlock
    simp only [addi, small, ite_true, mark, mov, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
      show 0 < 4096 from by decide, RegUpd.gpr_write, Size.bits,
      BitVec.setWidth_eq, BitVec.add_zero, h15,
      ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, ?_⟩
    constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.2, ite_false]
    all_goals rfl
  · apply WP.of_runBlock
    simp only [addi, small, ite_false, imm, hn, ite_true, mark, mov,
      List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
      show 0 < 4096 from by decide, Size.bits, Nat.reduceMul, Nat.reduceLT,
      BitVec.shiftLeft_zero, width, RegUpd.gpr_write, BitVec.setWidth_eq,
      hd, h15, BitVec.add_zero,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, ?_⟩
    constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
    all_goals rfl

theorem mov_ok (s : State) (d n : Reg) :
    WP isa (.block (mov d n)) s fun t =>
      t.gpr d = s.gpr n ∧ Divide.Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    show 0 < 4096 from by decide, Size.bits, BitVec.setWidth_eq,
    BitVec.add_zero, RegUpd.gpr_write, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem load_ok (s : State) (d n : Reg) (offset : Nat)
    (ha : offset % 8 = 0) (hb : offset < 32768)
    (read : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (load d n offset)) s fun t =>
      t.gpr d = s.mem.readW (s.gpr n + BitVec.ofNat 64 offset) 64 ∧
      Divide.Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [load, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, ha, hb, and_self, ite_true, State.load, read,
    Option.map_some, Option.bind_some, RegUpd.gpr_write, BitVec.setWidth_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  all_goals rfl

theorem pointer_ok (s : State) (d base : Reg) (n : Nat) (hn : n < 65536)
    (hd : d ≠ .x12) (h15 : d ≠ .x15) :
    WP isa (.block (mov d base ++ addi d n)) s fun t =>
      t.gpr d = s.gpr base + BitVec.ofNat 64 n ∧ Divide.Keeps [d, .x12, .x15] s t := by
  apply WP.block_append
  refine (mov_ok s d base).mono ?_
  rintro a ⟨value, keeps⟩
  refine (addi_ok a d n hn hd h15).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨out.trans (congrArg (· + BitVec.ofNat 64 n) value), ?_⟩
  exact (keeps.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)).trans kt

theorem compare_ok (s : State) (a b : Reg)
    (ha : (s.gpr a).toNat < 2 ^ 63) (hb : (s.gpr b).toNat < 2 ^ 63) :
    WP isa (.block (VG.Impl.Argon2.AArch64.Instructions.compare a b)) s fun t =>
      t.gpr .x14 = (BitVec.ofBool (decide ((s.gpr a).toNat < (s.gpr b).toNat))).setWidth 64 ∧
      Divide.Keeps [.x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.AArch64.Instructions.compare, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, BitVec.setWidth_eq, show (63 : Nat) < 64 from by decide,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, Bool.toNat_true, sub_value,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · rw [Divide.difference_high _ _ ha hb]
    by_cases h : (s.gpr a).toNat < (s.gpr b).toNat <;>
      simp only [h, decide_true, decide_false, ite_true, ite_false] <;> rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2, ite_false]
    all_goals rfl
theorem store_ok (s : State) (base source : Reg) (offset : Nat)
    (ha : offset % 8 = 0) (hb : offset < 32768)
    (write : InRegions s.wr (s.gpr base + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (store base offset source)) s fun t =>
      t.mem = s.mem.writeW (s.gpr base + BitVec.ofNat 64 offset) (s.gpr source) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [store, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, ha, hb, and_self, ite_true, State.store, write, State.read,
    BitVec.setWidth_eq, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, trivial⟩

theorem comparem_ok (s : State) (a base : Reg) (offset : Nat)
    (ha : offset % 8 = 0) (hb : offset < 32768) (ar : a ≠ .x13)
    (read : InRegions (s.rd ++ s.wr) (s.gpr base + BitVec.ofNat 64 offset) 8)
    (left : (s.gpr a).toNat < 2 ^ 63)
    (right : (s.mem.readW (s.gpr base + BitVec.ofNat 64 offset) 64).toNat < 2 ^ 63) :
    WP isa (.block (comparem a base offset)) s fun t =>
      eval (.nonzero .x .x14) t = some (decide ((s.gpr a).toNat <
        (s.mem.readW (s.gpr base + BitVec.ofNat 64 offset) 64).toNat)) ∧
      Divide.Keeps [.x13, .x14, .x15] s t := by
  unfold comparem
  apply WP.block_append
  refine (load_ok s .x13 base offset ha hb read).mono ?_
  rintro u ⟨loaded, keeps⟩
  have preserved := keeps.regs a (by simpa only [List.mem_singleton] using ar)
  have leftU : (u.gpr a).toNat < 2 ^ 63 := by rw [preserved]; exact left
  have rightU : (u.gpr .x13).toNat < 2 ^ 63 := by rw [loaded]; exact right
  refine (compare_ok u a .x13 leftU rightU).mono ?_
  rintro t ⟨value, changed⟩
  refine ⟨?_, (keeps.mono (by decide)).trans (changed.mono (by decide))⟩
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, value, preserved, loaded]
  cases decide ((s.gpr a).toNat < (s.mem.readW (s.gpr base + BitVec.ofNat 64 offset) 64).toNat) <;> rfl

theorem add_ok (s : State) (d n : Reg) (h15 : d ≠ .x15) :
    WP isa (.block (add d n)) s fun t =>
      t.gpr d = s.gpr d + s.gpr n ∧ Divide.Keeps [d, .x15] s t := by
  apply WP.of_runBlock
  simp only [add, mark, mov, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 0 < 4096 from by decide, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, h15, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem subi_ok (s : State) (d : Reg) (n : Nat) (hn : n < 65536)
    (hd : d ≠ .x12) (h15 : d ≠ .x15) :
    WP isa (.block (subi d n)) s fun t =>
      t.gpr d = s.gpr d - BitVec.ofNat 64 n ∧
      t.gpr .x15 = s.gpr d - BitVec.ofNat 64 n ∧ Divide.Keeps [d, .x12, .x15] s t := by
  have width : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n :=
    BitVec.setWidth_ofNat_of_le_of_lt (by decide) hn
  apply WP.of_runBlock
  simp only [subi, sub, imm, hn, ite_true, mark, mov, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 0 < 4096 from by decide, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hd, h15, width,
    sub_value, Bool.toNat_true, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.AArch64.Instructions
