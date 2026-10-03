import VerifiedGarbage.Proof.Argon2.AArch64.Mix
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-! # Argon2 compression working memory -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Impl.Argon2.AArch64

abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d
abbrev word (m : Mem) (p : Addr) (i : Nat) : BitVec 64 := m.readW (off p (1024 + 8 * i)) 64

/-- Scratch permissions and its stable base register. -/
structure Scratch (s : State) (p : Addr) : Prop where
  reg : s.gpr .x3 = p
  wr : (⟨p, 4096⟩ : Region) ∈ s.wr

theorem Scratch.write {s : State} {p : Addr} (h : Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions s.wr (off p d) n :=
  ⟨_, h.wr, Offset.contains_base p hd (by omega)⟩

theorem Scratch.read {s : State} {p : Addr} (h : Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions (s.rd ++ s.wr) (off p d) n :=
  ⟨_, List.mem_append_right _ h.wr, Offset.contains_base p hd (by omega)⟩

theorem word_offset (i : Nat) (hi : i < 128) :
    (1024 + 8 * i) % 8 = 0 ∧ 1024 + 8 * i < 32768 := by omega

/-- Load the four words of GB without changing memory or any other register. -/
theorem loadGB_ok (s : State) {p : Addr} (hs : Scratch s p) {a b c d : Nat}
    (ha : a < 128) (hb : b < 128) (hc : c < 128) (hd : d < 128) :
    WP isa (.block [
      .ldr .x .x4 .x3 (1024 + 8 * a),
      .ldr .x .x5 .x3 (1024 + 8 * b),
      .ldr .x .x6 .x3 (1024 + 8 * c),
      .ldr .x .x7 .x3 (1024 + 8 * d)]) s fun t =>
      t.gpr .x4 = word s.mem p a ∧ t.gpr .x5 = word s.mem p b ∧
      t.gpr .x6 = word s.mem p c ∧ t.gpr .x7 = word s.mem p d ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have la := hs.read (d := 1024 + 8 * a) (n := 8) (by omega)
  have lb := hs.read (d := 1024 + 8 * b) (n := 8) (by omega)
  have lc := hs.read (d := 1024 + 8 * c) (n := 8) (by omega)
  have ld := hs.read (d := 1024 + 8 * d) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x (word_offset a ha),
    exec_ldr_x (word_offset b hb), exec_ldr_x (word_offset c hc), exec_ldr_x (word_offset d hd),
    hs.reg, la, lb, lc, ld, off, word, RegUpd.gpr_write,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, reduceCtorEq,
    ite_true, ite_false, Option.some.injEq, exists_eq_left', BitVec.setWidth_eq]
  exact ⟨trivial, trivial, trivial, trivial,
    fun r h1 h2 h3 h4 => by simp only [h1, h2, h3, h4, ite_false], trivial, trivial, trivial⟩

/-- Store the GB result in order, leaving all registers and permissions intact. -/
theorem storeGB_ok (s : State) {p : Addr} (hs : Scratch s p) {a b c d : Nat}
    (ha : a < 128) (hb : b < 128) (hc : c < 128) (hd : d < 128) :
    WP isa (.block [
      .str .x .x4 .x3 (1024 + 8 * a),
      .str .x .x5 .x3 (1024 + 8 * b),
      .str .x .x6 .x3 (1024 + 8 * c),
      .str .x .x7 .x3 (1024 + 8 * d)]) s fun t =>
      t.mem = (((s.mem.writeW (off p (1024 + 8 * a)) (s.gpr .x4)).writeW
        (off p (1024 + 8 * b)) (s.gpr .x5)).writeW
        (off p (1024 + 8 * c)) (s.gpr .x6)).writeW
        (off p (1024 + 8 * d)) (s.gpr .x7) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have wa := hs.write (d := 1024 + 8 * a) (n := 8) (by omega)
  have wb := hs.write (d := 1024 + 8 * b) (n := 8) (by omega)
  have wc := hs.write (d := 1024 + 8 * c) (n := 8) (by omega)
  have wd := hs.write (d := 1024 + 8 * d) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_str_x (word_offset a ha),
    exec_str_x (word_offset b hb), exec_str_x (word_offset c hc), exec_str_x (word_offset d hd),
    hs.reg, wa, wb, wc, wd, off, Option.some.injEq, exists_eq_left']
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
      (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 →
        r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
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
    rw [hk2 .x3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
      hk1 .x3 (by decide) (by decide) (by decide) (by decide), hs.reg]
  refine (storeGB_ok s2 hs2 ha hb hc hd).mono ?_
  rintro t ⟨hm3, hk3, hr3, hw3⟩
  refine ⟨?_, ?_, hr3.trans (hr2.trans hr1), hw3.trans (hw2.trans hw1)⟩
  · rw [hm3, ha2, hb2, hc2, hd2, ha1, hb1, hc1, hd1, hm2, hm1]
    rfl
  · intro r h8 h9 h10 h11 h0 hdx hsi
    rw [hk3, hk2 r h8 h9 h10 h11 h0 hdx hsi, hk1 r h8 h9 h10 h11]

end VG.Proof.Argon2.AArch64
