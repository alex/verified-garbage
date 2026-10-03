import VerifiedGarbage.Impl.Argon2.X86_64.AddressHeader
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
import VerifiedGarbage.Proof.Argon2.X86_64.Initialize

/-! Merged from `Proof.Argon2.X86_64.BlockStore`. -/
section
/-! A single matrix or scratch block word write as a vector update. -/

namespace VG.Proof.Argon2.X86_64

open VG VG.Spec.Argon2

theorem blockAt_write (m : Mem) (p : Addr) (i : Fin 128) (v : Word) :
    blockAt (m.writeW (off p (8 * i.val)) v) p = (blockAt m p).set i v := by
  apply Vector.ext
  intro j hj
  simp only [blockAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases eq : i.val = j
  · subst j
    simp only [ite_true]
    change (m.writeW (off p (8 * i.val)) v).readW (off p (8 * i.val)) 64 = v
    exact Mem.readW_writeW_self64 _ _ _
  · simp only [eq, ite_false]
    change (m.writeW (off p (8 * i.val)) v).readW (off p (8 * j)) 64 =
      m.readW (off p (8 * j)) 64
    exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem blockAt_write_nat (m : Mem) (p : Addr) (i : Nat) (hi : i < 128) (v : Word) :
    blockAt (m.writeW (off p (8 * i)) v) p = (blockAt m p).set i v hi :=
  blockAt_write m p ⟨i, hi⟩ v

end VG.Proof.Argon2.X86_64
end

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
