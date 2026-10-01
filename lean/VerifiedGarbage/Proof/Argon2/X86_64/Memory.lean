import VerifiedGarbage.Proof.Argon2.X86_64.Mix
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-! # Argon2 compression working memory -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Impl.Argon2.X86_64

abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d
abbrev word (m : Mem) (p : Addr) (i : Nat) : BitVec 64 := m.readW (off p (1024 + 8 * i)) 64

/-- Scratch permissions and its stable base register. -/
structure Scratch (s : State) (p : Addr) : Prop where
  reg : s.gpr .rcx = p
  wr : (⟨p, 4096⟩ : Region) ∈ s.wr

theorem Scratch.write {s : State} {p : Addr} (h : Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions s.wr (off p d) n :=
  ⟨_, h.wr, Offset.contains_base p hd (by omega)⟩

theorem Scratch.read {s : State} {p : Addr} (h : Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions (s.rd ++ s.wr) (off p d) n :=
  ⟨_, List.mem_append_right _ h.wr, Offset.contains_base p hd (by omega)⟩

theorem ea_at (s : State) (r : Reg) (d : Nat) :
    s.ea (at_ r d) = off (s.gpr r) d := by
  simp only [State.ea, at_, BitVec.ofInt_natCast]

/-- Load the four words of GB without changing memory or any other register. -/
theorem loadGB_ok (s : State) {p : Addr} (hs : Scratch s p) {a b c d : Nat}
    (ha : a < 128) (hb : b < 128) (hc : c < 128) (hd : d < 128) :
    WP isa (.block [
      .mov .r8 (.mem (at_ .rcx (1024 + 8 * a))),
      .mov .r9 (.mem (at_ .rcx (1024 + 8 * b))),
      .mov .r10 (.mem (at_ .rcx (1024 + 8 * c))),
      .mov .r11 (.mem (at_ .rcx (1024 + 8 * d)))]) s fun t =>
      t.gpr .r8 = word s.mem p a ∧ t.gpr .r9 = word s.mem p b ∧
      t.gpr .r10 = word s.mem p c ∧ t.gpr .r11 = word s.mem p d ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have la := hs.read (d := 1024 + 8 * a) (n := 8) (by omega)
  have lb := hs.read (d := 1024 + 8 * b) (n := 8) (by omega)
  have lc := hs.read (d := 1024 + 8 * c) (n := 8) (by omega)
  have ld := hs.read (d := 1024 + 8 * d) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, hs.reg, la, lb, lc, ld, reduceCtorEq,
    ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial,
    fun r h1 h2 h3 h4 => by simp only [h1, h2, h3, h4, ite_false], trivial, trivial, trivial⟩

/-- Store the GB result in order, leaving all registers and permissions intact. -/
theorem storeGB_ok (s : State) {p : Addr} (hs : Scratch s p) {a b c d : Nat}
    (ha : a < 128) (hb : b < 128) (hc : c < 128) (hd : d < 128) :
    WP isa (.block [
      .store (at_ .rcx (1024 + 8 * a)) .r8,
      .store (at_ .rcx (1024 + 8 * b)) .r9,
      .store (at_ .rcx (1024 + 8 * c)) .r10,
      .store (at_ .rcx (1024 + 8 * d)) .r11]) s fun t =>
      t.mem = (((s.mem.writeW (off p (1024 + 8 * a)) (s.gpr .r8)).writeW
        (off p (1024 + 8 * b)) (s.gpr .r9)).writeW
        (off p (1024 + 8 * c)) (s.gpr .r10)).writeW
        (off p (1024 + 8 * d)) (s.gpr .r11) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have wa := hs.write (d := 1024 + 8 * a) (n := 8) (by omega)
  have wb := hs.write (d := 1024 + 8 * b) (n := 8) (by omega)
  have wc := hs.write (d := 1024 + 8 * c) (n := 8) (by omega)
  have wd := hs.write (d := 1024 + 8 * d) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    ea_at, hs.reg, wa, wb, wc, wd, ite_true, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- Four stores implementing one GB in scratch. -/
def storeMix (m : Mem) (p : Addr) (a b c d : Nat)
    (v : Spec.Argon2.Word × Spec.Argon2.Word × Spec.Argon2.Word × Spec.Argon2.Word) : Mem :=
  (((m.writeW (off p (1024 + 8 * a)) v.1).writeW
    (off p (1024 + 8 * b)) v.2.1).writeW
    (off p (1024 + 8 * c)) v.2.2.1).writeW
    (off p (1024 + 8 * d)) v.2.2.2

/-- The complete load/mix/store operation, independently of surrounding words. -/
theorem gbAt_ok (s : State) {p : Addr} (hs : Scratch s p) {a b c d : Nat}
    (ha : a < 128) (hb : b < 128) (hc : c < 128) (hd : d < 128) :
    WP isa (gbAt a b c d) s fun t =>
      t.mem = storeMix s.mem p a b c d
        (Proof.Argon2.mix (word s.mem p a) (word s.mem p b)
          (word s.mem p c) (word s.mem p d)) ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .rax → r ≠ .rdx → r ≠ .rsi → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  rw [gbAt]
  apply WP.seq
  refine (loadGB_ok s hs ha hb hc hd).mono ?_
  rintro s1 ⟨ha1, hb1, hc1, hd1, hk1, hm1, hr1, hw1⟩
  apply WP.seq
  refine (gb_ok s1).mono ?_
  rintro s2 ⟨ha2, hb2, hc2, hd2, hk2, hm2, hr2, hw2⟩
  have hs2 : Scratch s2 p := by
    refine ⟨?_, (hw2.trans hw1) ▸ hs.wr⟩
    rw [hk2 .rcx (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
      hk1 .rcx (by decide) (by decide) (by decide) (by decide), hs.reg]
  refine (storeGB_ok s2 hs2 ha hb hc hd).mono ?_
  rintro t ⟨hm3, hk3, hr3, hw3⟩
  refine ⟨?_, ?_, hr3.trans (hr2.trans hr1), hw3.trans (hw2.trans hw1)⟩
  · rw [hm3, ha2, hb2, hc2, hd2, ha1, hb1, hc1, hd1, hm2, hm1]
    rfl
  · intro r h8 h9 h10 h11 h0 hdx hsi
    rw [hk3, hk2 r h8 h9 h10 h11 h0 hdx hsi, hk1 r h8 h9 h10 h11]

end VG.Proof.Argon2.X86_64
