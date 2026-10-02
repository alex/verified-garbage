import VerifiedGarbage.Impl.Argon2.X86_64.FillWrite
import VerifiedGarbage.Proof.Argon2.X86_64.Memory
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep

/-! One output word, keeping register writes folded during execution. -/

namespace VG.Proof.Argon2.X86_64.FillWrite

open VG VG.X86_64 VG.Impl.Argon2.X86_64.FillWrite

def value (xorOld : Bool) (m : Mem) (src dest : Addr) (i : Nat) : Addr :=
  let next := m.readW (off src (8 * i)) 64
  if xorOld then next ^^^ m.readW (off dest (8 * i)) 64 else next

/-- The source is readable and the destination writable; its old contents
are read only on later passes. -/
theorem word_ok (xorOld : Bool) (s : State) (i : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rsi) (8 * i)) 8)
    (hw : InRegions s.wr (off (s.gpr .rdi) (8 * i)) 8)
    (ho : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) (8 * i)) 8) :
    WP isa (.block (Impl.Argon2.X86_64.FillWrite.word xorOld i)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rdi) (8 * i))
        (value xorOld s.mem (s.gpr .rsi) (s.gpr .rdi) i) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  cases xorOld <;> apply WP.of_runBlock <;>
    simp only [Impl.Argon2.X86_64.FillWrite.word, value, Bool.false_eq_true, ite_false, ite_true,
      List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load64, State.store64, execAlu, ea_at, hr, hw, ho,
      RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
      RegUpd.wr_arithFlags, reduceCtorEq, ite_true, ite_false,
      Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  all_goals
    refine ⟨trivial, ?_, trivial, trivial, rfl⟩
    intro r hr
    simp only [hr, ite_false]

end VG.Proof.Argon2.X86_64.FillWrite
