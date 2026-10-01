import VerifiedGarbage.Impl.Argon2.X86_64.Initial
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! # Argument handling for Argon2 H₀ -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Impl.Argon2.X86_64.HPrime (at_)

theorem ea_at (s : State) (r : Reg) (d : Nat) :
    s.ea (at_ r d) = s.gpr r + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, BitVec.ofInt_natCast]

theorem headerWord_ok (s : State) (source destination : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 source) 8)
    (hw : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 destination) 4) :
    WP isa (.block (headerWord source destination)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 destination)
        ((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 source) 64).setWidth 32) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [headerWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, State.store32, ea_at, RegUpd.gpr_setReg, RegUpd.wr_setReg,
    RegUpd.rd_setReg, RegUpd.mem_setReg, hr, hw, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, trivial, trivial⟩
  intro r hr
  simp only [hr, ite_false]

structure LengthArgs (s : State) (offset : Nat) (t : State) : Prop where
  length : t.gpr .r14 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 offset) 64
  count : t.gpr .rsi = s.gpr .r12
  pointer : t.gpr .rdx = s.gpr .rbx + 792
  size : t.gpr .rcx = 4
  other : ∀ r, r ≠ .r14 → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem.writeW (s.gpr .rbx + 792)
    ((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 offset) 64).setWidth 32)
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem lengthArgs_ok (s : State) (offset : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 offset) 8)
    (hw : InRegions s.wr (s.gpr .rbx + 792) 4) :
    WP isa (.block (lengthArgs offset)) s (LengthArgs s offset) := by
  apply WP.of_runBlock
  simp only [lengthArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, State.setReg32, State.load64, State.store32, execAlu, ea_at,
    RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.rd_setReg,
    RegUpd.mem_setReg, hr, hw, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    show BitVec.ofNat 64 792 = (792 : Addr) from rfl]
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro r h1 h2 h3 h4
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, h3, h4, ite_false]

structure InputArgs (s t : State) (offset : Nat) : Prop where
  total : t.gpr .r12 = s.gpr .r12 + 4
  count : t.gpr .rsi = s.gpr .r12 + 4
  pointer : t.gpr .rdx = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 offset) 64
  length : t.gpr .rcx = s.gpr .r14
  other : ∀ r, r ≠ .r12 → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem inputArgs_ok (s : State) (offset : Nat)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (inputArgs offset)) s (fun t => InputArgs s t offset) := by
  apply WP.of_runBlock
  simp only [inputArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, execAlu, ea_at, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags, hr, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro r h1 h2 h3 h4
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, h3, h4, ite_false]

end VG.Proof.Argon2.X86_64.Initial
