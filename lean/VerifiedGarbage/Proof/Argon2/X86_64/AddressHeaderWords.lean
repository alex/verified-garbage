import VerifiedGarbage.Impl.Argon2.X86_64.AddressHeader
import VerifiedGarbage.Proof.Argon2.X86_64.BlockStore
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep

/-! Short independent-address input header writes. -/

namespace VG.Proof.Argon2.X86_64.AddressHeader

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressHeader

theorem registerWord_ok (s : State) (i : Nat) (r : Reg)
    (hw : InRegions s.wr (off (s.gpr .rdi) (8 * i)) 8) :
    WP isa (.block (registerWord i r)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rdi) (8 * i)) (s.gpr r) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [registerWord, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.store64, ea_at, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem frameWord_ok (s : State) (i offset : Nat)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) offset) 8)
    (hw : InRegions s.wr (off (s.gpr .rdi) (8 * i)) 8) :
    WP isa (.block (frameWord i offset)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rdi) (8 * i))
        (s.mem.readW (off (s.gpr .rbp) offset) 64) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [frameWord, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, State.load64, State.store64, ea_at, hr, hw,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, trivial, trivial, rfl⟩
  intro r hr
  simp only [hr, ite_false]

end VG.Proof.Argon2.X86_64.AddressHeader
