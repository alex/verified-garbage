import VerifiedGarbage.Proof.Argon2.AArch64.Words

/-! # Initial XOR and final XOR, one word at a time -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Impl.Argon2.AArch64

theorem initWord_ok (s : State) {p : Addr} (hs : Scratch s p) (i : Fin 128)
    (hx : InRegions (s.rd ++ s.wr) (off (s.gpr .x0) (8 * i.val)) 8)
    (hy : InRegions (s.rd ++ s.wr) (off (s.gpr .x1) (8 * i.val)) 8) :
    let v := s.mem.readW (off (s.gpr .x0) (8 * i.val)) 64 ^^^
      s.mem.readW (off (s.gpr .x1) (8 * i.val)) 64
    WP isa (.block (initWord i.val)) s fun t =>
      t.mem = (s.mem.writeW (off p (8 * i.val)) v).writeW (off p (1024 + 8 * i.val)) v ∧
      (∀ r, r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  dsimp only
  have w1 := hs.write (d := 8 * i.val) (n := 8) (by omega)
  have w2 := hs.write (d := 1024 + 8 * i.val) (n := 8) (by omega)
  have e1 : (8 * i.val) % 8 = 0 ∧ 8 * i.val < 32768 := by omega
  have e2 := word_offset i.val i.isLt
  apply WP.of_runBlock
  simp only [initWord, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, e1, e2, and_self, ite_true, Option.bind_some,
    State.load, State.store, off, hs.reg, hx, hy, w1, w2, State.read,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    Mem.readW, Mem.writeW, reduceCtorEq, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left', BitVec.setWidth_eq]
  exact ⟨trivial, fun r hr hr9 => by simp only [hr, hr9, ite_false], trivial⟩

theorem finishWord_ok (s : State) {p : Addr} (hs : Scratch s p) (i : Fin 128)
    (hout : InRegions s.wr (off (s.gpr .x2) (8 * i.val)) 8) :
    WP isa (.block (finishWord i.val)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .x2) (8 * i.val))
        (word s.mem p i.val ^^^ s.mem.readW (off p (8 * i.val)) 64) ∧
      (∀ r, r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have r1 := hs.read (d := 8 * i.val) (n := 8) (by omega)
  have r2 := hs.read (d := 1024 + 8 * i.val) (n := 8) (by omega)
  have e1 : (8 * i.val) % 8 = 0 ∧ 8 * i.val < 32768 := by omega
  have e2 := word_offset i.val i.isLt
  apply WP.of_runBlock
  simp only [finishWord, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, e1, e2, and_self, ite_true, Option.bind_some,
    State.load, State.store, off, hs.reg, hout, r1, r2, State.read,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    Mem.readW, Mem.writeW, reduceCtorEq, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left', BitVec.setWidth_eq]
  exact ⟨trivial, fun r hr hr9 => by simp only [hr, hr9, ite_false], trivial⟩

end VG.Proof.Argon2.AArch64
