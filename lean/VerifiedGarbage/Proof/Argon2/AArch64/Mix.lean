import VerifiedGarbage.Proof.Argon2.Spec
import VerifiedGarbage.Impl.Argon2.AArch64.Compress
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # Argon2's modified addition on ARM64 -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Impl.Argon2.AArch64

theorem low32 (x : BitVec 64) :
    (x.setWidth 32).setWidth 64 = x &&& 0xffffffff := by
  rw [BitVec.setWidth_eq_append (by decide)]
  exact (BitVec.and_setWidth_allOnes 32 32 x).symm

theorem addMul_value (a b : BitVec 64) :
    a + b + (a.setWidth 32).setWidth 64 * (b.setWidth 32).setWidth 64 +
      (a.setWidth 32).setWidth 64 * (b.setWidth 32).setWidth 64 =
      Spec.Argon2.addMul a b := by
  rw [low32, low32, BitVec.add_assoc, ← BitVec.two_mul, Spec.Argon2.addMul,
    BitVec.mul_assoc]
  rfl

theorem addMul_ok {a b : Reg}
    (ha0 : a ≠ .x8) (_ha2 : a ≠ .x9) (ha6 : a ≠ .x10)
    (hb0 : b ≠ .x8) (_hb2 : b ≠ .x9) (hb6 : b ≠ .x10)
    (s : State) :
    WP isa (.block (addMul a b)) s fun t =>
      t.gpr a = Spec.Argon2.addMul (s.gpr a) (s.gpr b) ∧
      (∀ r, r ≠ a → r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [addMul, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    ha0, ha6, hb0, hb6, ha0.symm, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left', BitVec.setWidth_eq, BitVec.or_self]
  refine ⟨addMul_value _ _, ?_, trivial, trivial, trivial⟩
  intro r h1 h2 h3 h4
  simp only [h1, h2, h4, ite_false]

/-- A register XOR followed by one of GB's rotations. -/
theorem xorRotate_ok {a d : Reg} (n : Nat)
    (hn : 1 ≤ n) (hn' : n ≤ 63) (s : State) :
    WP isa (.block [.logic .eor .x d d a, .ror .x d d n]) s fun t =>
      t.gpr d = (s.gpr d ^^^ s.gpr a).rotateRight n ∧
      (∀ r, r ≠ d → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  have h64 : n < 64 := by omega
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    h64, ite_true, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq]
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial, trivial⟩

/-- One half of GB, with all memory and non-working registers preserved. -/
theorem halfGB_ok (r1 r2 : Nat) (h1 : 1 ≤ r1) (h1' : r1 ≤ 63)
    (h2 : 1 ≤ r2) (h2' : r2 ≤ 63) (s : State) :
    let a := Spec.Argon2.addMul (s.gpr .x4) (s.gpr .x5)
    let d := (s.gpr .x7 ^^^ a).rotateRight r1
    let c := Spec.Argon2.addMul (s.gpr .x6) d
    let b := (s.gpr .x5 ^^^ c).rotateRight r2
    WP isa (.block (halfGB r1 r2)) s fun t =>
      t.gpr .x4 = a ∧ t.gpr .x5 = b ∧ t.gpr .x6 = c ∧ t.gpr .x7 = d ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 →
        r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  dsimp only
  rw [halfGB, List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine (addMul_ok (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s).mono ?_
  rintro s1 ⟨ha, hk1, hm1, hr1, hw1⟩
  apply WP.block_append
  refine (xorRotate_ok r1 h1 h1' s1).mono ?_
  rintro s2 ⟨hd, hk2, hm2, hr2, hw2⟩
  apply WP.block_append
  refine (addMul_ok (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s2).mono ?_
  rintro s3 ⟨hc, hk3, hm3, hr3, hw3⟩
  refine (xorRotate_ok r2 h2 h2' s3).mono ?_
  rintro s4 ⟨hb, hk4, hm4, hr4, hw4⟩
  have hd' : s2.gpr .x7 =
      (s.gpr .x7 ^^^ Spec.Argon2.addMul (s.gpr .x4) (s.gpr .x5)).rotateRight r1 := by
    rw [hd, ha, hk1 .x7 (by decide) (by decide) (by decide) (by decide)]
  have hc' : s3.gpr .x6 = Spec.Argon2.addMul (s.gpr .x6) (s2.gpr .x7) := by
    rw [hc, hk2 .x6 (by decide), hk1 .x6 (by decide) (by decide) (by decide) (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, hm4.trans (hm3.trans (hm2.trans hm1)),
    hr4.trans (hr3.trans (hr2.trans hr1)), hw4.trans (hw3.trans (hw2.trans hw1))⟩
  · rw [hk4 .x4 (by decide), hk3 .x4 (by decide) (by decide) (by decide) (by decide),
      hk2 .x4 (by decide), ha]
  · rw [hb, hc', hd', hk3 .x5 (by decide) (by decide) (by decide) (by decide),
      hk2 .x5 (by decide), hk1 .x5 (by decide) (by decide) (by decide) (by decide)]
  · rw [hk4 .x6 (by decide), hc', hd']
  · rw [hk4 .x7 (by decide), hk3 .x7 (by decide) (by decide) (by decide) (by decide), hd']
  · intro r h8 h9 h10 h11 h0 hdx hsi
    rw [hk4 r h9, hk3 r h10 h0 hdx hsi, hk2 r h11, hk1 r h8 h0 hdx hsi]

/-- The complete GB operation agrees with the four-word specification. -/
theorem gb_ok (s : State) :
    let v := Proof.Argon2.mix (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
    WP isa (.block gb) s fun t =>
      t.gpr .x4 = v.1 ∧ t.gpr .x5 = v.2.1 ∧
      t.gpr .x6 = v.2.2.1 ∧ t.gpr .x7 = v.2.2.2 ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 →
        r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  dsimp only
  rw [gb]
  apply WP.block_append
  refine (halfGB_ok 32 24 (by decide) (by decide) (by decide) (by decide) s).mono ?_
  rintro t ⟨ha, hb, hc, hd, hk, hm, hr, hw⟩
  refine (halfGB_ok 16 63 (by decide) (by decide) (by decide) (by decide) t).mono ?_
  rintro u ⟨ha', hb', hc', hd', hk', hm', hr', hw'⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hm'.trans hm, hr'.trans hr, hw'.trans hw⟩
  · rw [ha', ha, hb]; rfl
  · rw [hb', ha, hb, hc, hd]; rfl
  · rw [hc', ha, hb, hc, hd]; rfl
  · rw [hd', ha, hb, hd]; rfl
  · intro r h8 h9 h10 h11 h0 hdx hsi
    exact (hk' r h8 h9 h10 h11 h0 hdx hsi).trans (hk r h8 h9 h10 h11 h0 hdx hsi)

end VG.Proof.Argon2.AArch64
