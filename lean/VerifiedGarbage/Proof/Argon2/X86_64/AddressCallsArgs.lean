import VerifiedGarbage.Impl.Argon2.X86_64.AddressCalls
import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderWords

/-! Independent-address compression arguments from one fixed frame read. -/

namespace VG.Proof.Argon2.X86_64.AddressCalls

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCalls

def work (s : State) : Addr := s.mem.readW (off (s.gpr .rbp) 248) 64

def displacement (n : Nat) : Addr := BitVec.signExtend 64 (BitVec.ofNat 32 n)

theorem pointer_ok (s : State) (offset : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8) :
    WP isa (.block (pointer offset)) s fun t =>
      t.gpr .rdi = work s + displacement offset ∧ Divide.Keeps [.rdi] s t := by
  apply WP.of_runBlock
  simp only [pointer, work, displacement, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, ea_at, hr, execAlu, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, ite_true, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem args_ok (s : State) (x y out : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8) :
    WP isa (.block (args x y out)) s fun t =>
      t.gpr .rcx = work s ∧ t.gpr .rdi = work s + displacement x ∧
      t.gpr .rsi = work s + displacement y ∧ t.gpr .rdx = work s + displacement out ∧
      Divide.Keeps [.rcx, .rdi, .rsi, .rdx] s t := by
  apply WP.of_runBlock
  simp only [args, work, displacement, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, ea_at, hr, execAlu, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, reduceCtorEq, ite_true, ite_false, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2, ite_false]
  all_goals rfl

end VG.Proof.Argon2.X86_64.AddressCalls
