import VerifiedGarbage.Proof.Argon2.X86_64.Words

/-! # Initial XOR and final XOR, one word at a time -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Impl.Argon2.X86_64

theorem initWord_ok (s : State) {p : Addr} (hs : Scratch s p) (i : Fin 128)
    (hx : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) (8 * i.val)) 8)
    (hy : InRegions (s.rd ++ s.wr) (off (s.gpr .rsi) (8 * i.val)) 8) :
    let v := s.mem.readW (off (s.gpr .rdi) (8 * i.val)) 64 ^^^
      s.mem.readW (off (s.gpr .rsi) (8 * i.val)) 64
    WP isa (.block (initWord i.val)) s fun t =>
      t.mem = (s.mem.writeW (off p (8 * i.val)) v).writeW (off p (1024 + 8 * i.val)) v ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  dsimp only
  have w1 := hs.write (d := 8 * i.val) (n := 8) (by omega)
  have w2 := hs.write (d := 1024 + 8 * i.val) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [initWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, State.store64, execAlu, ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    hs.reg, hx, hy, w1, w2, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial⟩

theorem finishWord_ok (s : State) {p : Addr} (hs : Scratch s p) (i : Fin 128)
    (hout : InRegions s.wr (off (s.gpr .rdi) (8 * i.val)) 8) :
    WP isa (.block (finishWord i.val)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rdi) (8 * i.val))
        (word s.mem p i.val ^^^ s.mem.readW (off p (8 * i.val)) 64) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have r1 := hs.read (d := 8 * i.val) (n := 8) (by omega)
  have r2 := hs.read (d := 1024 + 8 * i.val) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [finishWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, State.store64, execAlu, ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    hs.reg, hout, r1, r2, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial⟩

end VG.Proof.Argon2.X86_64
