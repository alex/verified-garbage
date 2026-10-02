import VerifiedGarbage.Proof.Ed25519.AArch64.Row
import VerifiedGarbage.Proof.Ed25519.AArch64.Reduce

/-! Four-by-four word field multiplication and its memory frame. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

theorem row0 (a b : Nat) : row a b 0 = rowR a b 0 .x4 .x5 .x6 .x7 .x21 := row_eq a b 0
theorem row1 (a b : Nat) : row a b 1 = rowR a b 1 .x5 .x6 .x7 .x21 .x22 := row_eq a b 1
theorem row2 (a b : Nat) : row a b 2 = rowR a b 2 .x6 .x7 .x21 .x22 .x23 := row_eq a b 2
theorem row3 (a b : Nat) : row a b 3 = rowR a b 3 .x7 .x21 .x22 .x23 .x24 := row_eq a b 3

theorem fe_mul_expand (m : Mem) (base : Addr) (a B : Nat) :
    fe m base a * B = (word m base (a + 8 * 0)).toNat * B + 2 ^ 64 * ((word m base (a + 8 * 1)).toNat * B) +
      2 ^ 128 * ((word m base (a + 8 * 2)).toNat * B) + 2 ^ 192 * ((word m base (a + 8 * 3)).toNat * B) := by
  simp only [fe, val4, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul,
    Nat.add_mul, Nat.mul_assoc]

def wideClob : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x20, .x21, .x22, .x23, .x24]

theorem rowsAccumulate_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : FieldRange a) (hb : FieldRange b) (hz : s.gpr .x10 = 0) :
    WP isa (.block (row a b 0 ++ (row a b 1 ++ (row a b 2 ++ row a b 3)))) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) +
        2 ^ 256 * val4 (t.gpr .x21) (t.gpr .x22) (t.gpr .x23) (t.gpr .x24) =
          val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) +
            fe s.mem base a * fe s.mem base b ∧ Keeps wideClob s t := by
  obtain ⟨haa, ha⟩ := ha
  obtain ⟨hba, hb⟩ := hb
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.gpr r h
  rw [WP.block_append_iff, row0]
  refine WP.mono (rowR_ok hs (by omega) hb haa hba hz (by decide)) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  have hz1 := (g k1 .x10 (by decide)).trans hz
  rw [WP.block_append_iff, row1]
  refine WP.mono (rowR_ok hs₁ (by omega) hb haa hba hz1 (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  have hz2 := (g k2 .x10 (by decide)).trans hz1
  rw [WP.block_append_iff, row2]
  refine WP.mono (rowR_ok hs₂ (by omega) hb haa hba hz2 (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  have hz3 := (g k3 .x10 (by decide)).trans hz2
  rw [row3]
  refine WP.mono (rowR_ok hs₃ (by omega) hb haa hba hz3 (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  have K : Keeps wideClob s s₄ :=
    ((k1.mono (by decide)).trans (k2.mono (by decide))).trans
      (k3.mono (by decide)) |>.trans (k4.mono (by decide))
  refine ⟨?_, K⟩
  rw [fe_mul_expand]
  rw [k1.mem] at e2
  rw [k2.mem, k1.mem] at e3
  rw [k3.mem, k2.mem, k1.mem] at e4
  have r1 := g k2 .x4 (by decide)
  have r2 := g k3 .x4 (by decide)
  have r3 := g k4 .x4 (by decide)
  have q2 := g k3 .x5 (by decide)
  have q3 := g k4 .x5 (by decide)
  have q4 := g k4 .x6 (by decide)
  simp only [val4] at e1 e2 e3 e4 ⊢
  rw [r3, r2, r1, q3, q2, q4]
  omega_using [e1, e2, e3, e4]

/-- Rows 1–3 and the loads keep the words of `b` (x12–x15), x4 and x10. -/
def mulRowClob : List Reg :=
  [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x16, .x21, .x22, .x23, .x24]

theorem fe_mul_expand4 (A0 A1 A2 A3 B : Nat) :
    (A0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3) * B =
      A0 * B + 2 ^ 64 * (A1 * B) + 2 ^ 128 * (A2 * B) + 2 ^ 192 * (A3 * B) := by
  simp only [Nat.add_mul, Nat.mul_assoc]

theorem mulWide_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : FieldRange a) (hb : FieldRange b) (hz : s.gpr .x10 = 0) :
    WP isa (.block (mulWide a b)) s fun t =>
      wide t = fe s.mem base a * fe s.mem base b ∧
      Keeps (.x12 :: .x13 :: .x14 :: .x15 :: mulRowClob) s t := by
  obtain ⟨haa, ha'⟩ := ha
  simp only [mulWide, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs ⟨hb.1, hb.2⟩ (by decide)) fun s₁ ⟨b0, b1, b2, b3, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs₁ (by omega) (by omega) .x3) fun s₂ ⟨a0, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rowFirst_ok s₂ ((k2.gpr _ (by decide)).trans hz1)) fun s₃ ⟨e0, k3⟩ => ?_
  have K3 : Keeps mulRowClob s₁ s₃ := (k2.mono (by decide)).trans (k3.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs₁.of_keeps K3 (by decide)) (by omega) (by omega) .x3)
    fun s₄ ⟨a1, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rowAcc1_ok s₄ ((K3.trans (k4.mono (by decide))).gpr _ (by decide) |>.trans hz1))
    fun s₅ ⟨e1, k5⟩ => ?_
  have K5 : Keeps mulRowClob s₁ s₅ := (K3.trans (k4.mono (by decide))).trans (k5.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs₁.of_keeps K5 (by decide)) (by omega) (by omega) .x3)
    fun s₆ ⟨a2, k6⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rowAcc2_ok s₆ ((K5.trans (k6.mono (by decide))).gpr _ (by decide) |>.trans hz1))
    fun s₇ ⟨e2, k7⟩ => ?_
  have K7 : Keeps mulRowClob s₁ s₇ := (K5.trans (k6.mono (by decide))).trans (k7.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs₁.of_keeps K7 (by decide)) (by omega) (by omega) .x3)
    fun s₈ ⟨a3, k8⟩ => ?_
  refine WP.mono (rowAcc3_ok s₈ ((K7.trans (k8.mono (by decide))).gpr _ (by decide) |>.trans hz1))
    fun s₉ ⟨e3, k9⟩ => ?_
  have K9 : Keeps mulRowClob s₁ s₉ := (K7.trans (k8.mono (by decide))).trans (k9.mono (by decide))
  refine ⟨?_, (k1.mono (by decide)).trans (K9.mono (by decide))⟩
  -- The words of `a` and `b` at each row, and where each word of the result was last written.
  have B : ∀ (t : State), Keeps mulRowClob s₁ t →
      val4 (t.gpr .x12) (t.gpr .x13) (t.gpr .x14) (t.gpr .x15) = fe s.mem base b := by
    intro t k
    rw [k.gpr .x12 (by decide), k.gpr .x13 (by decide), k.gpr .x14 (by decide),
      k.gpr .x15 (by decide), b0, b1, b2, b3]
  rw [B s₂ (k2.mono (by decide)), a0, k1.mem] at e0
  rw [B s₄ (K3.trans (k4.mono (by decide))), a1, K3.mem, k1.mem, k4.gpr .x5 (by decide),
    k4.gpr .x6 (by decide), k4.gpr .x7 (by decide), k4.gpr .x21 (by decide)] at e1
  rw [B s₆ (K5.trans (k6.mono (by decide))), a2, K5.mem, k1.mem, k6.gpr .x6 (by decide),
    k6.gpr .x7 (by decide), k6.gpr .x21 (by decide), k6.gpr .x22 (by decide)] at e2
  rw [B s₈ (K7.trans (k8.mono (by decide))), a3, K7.mem, k1.mem, k8.gpr .x7 (by decide),
    k8.gpr .x21 (by decide), k8.gpr .x22 (by decide), k8.gpr .x23 (by decide)] at e3
  have K39 : Keeps [.x2, .x3, .x5, .x6, .x7, .x8, .x9, .x16, .x21, .x22, .x23, .x24] s₃ s₉ :=
    (((((k4.mono (by decide)).trans (k5.mono (by decide))).trans (k6.mono (by decide))).trans
      (k7.mono (by decide))).trans (k8.mono (by decide))).trans (k9.mono (by decide))
  have K59 : Keeps [.x2, .x3, .x6, .x7, .x8, .x9, .x16, .x21, .x22, .x23, .x24] s₅ s₉ :=
    (((k6.mono (by decide)).trans (k7.mono (by decide))).trans (k8.mono (by decide))).trans
      (k9.mono (by decide))
  have K79 : Keeps [.x2, .x3, .x7, .x8, .x9, .x16, .x21, .x22, .x23, .x24] s₇ s₉ :=
    (k8.mono (by decide)).trans (k9.mono (by decide))
  have hf : fe s.mem base a * fe s.mem base b =
      (word s.mem base a).toNat * fe s.mem base b +
        2 ^ 64 * ((word s.mem base (a + 8)).toNat * fe s.mem base b) +
        2 ^ 128 * ((word s.mem base (a + 16)).toNat * fe s.mem base b) +
        2 ^ 192 * ((word s.mem base (a + 24)).toNat * fe s.mem base b) :=
    fe_mul_expand4 _ _ _ _ _
  dsimp only [wide]
  rw [hf, K39.gpr .x4 (by decide), K59.gpr .x5 (by decide), K79.gpr .x6 (by decide)]
  generalize fe s.mem base b = FB at e0 e1 e2 e3 ⊢
  simp only [val4] at e0 e1 e2 e3 ⊢
  omega_using [e0, e1, e2, e3]

theorem zeroReg_ok (s : State) (r : Reg) :
    WP isa (.block [.movz .w r 0 0]) s fun t => t.gpr r = 0 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun q hq => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hq)

/-- Reduce the eight words of a product and store the result at `o`. -/
theorem fieldFinish_ok {s₀ s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : FieldRange o) (hz : s.gpr .x10 = 0) (k : Keeps clob s₀ s) :
    WP isa (.block (reduceWide ++ store4 o)) s fun t =>
      Op base o s₀ t ∧ F t.mem base o = toFe (wide s) := by
  rw [WP.block_append_iff]
  refine WP.mono (reduceWide_ok s hz) fun s₁ ⟨e1, _, k1⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps k1 (by decide)) ho) fun s₂ heq => ?_
  subst s₂
  refine ⟨Op.of_store ho (k.trans (k1.mono (by decide))) _ _ _ _, ?_⟩
  simp only [F]
  rw [fe_st4 _ _ (by have := ho.2; omega)]
  exact e1

/-- Multiplication modulo p, allowing the output to alias either input. -/
theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : FieldRange o) (ha : FieldRange a) (hb : FieldRange b) :
    WP isa (.block (fieldMul o a b)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  rw [fieldMul, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zeroReg_ok s .x10) fun s₀ ⟨hz, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulWide_ok hs₀ ha hb hz) fun s₁ ⟨e1, k1⟩ => ?_
  refine WP.mono (fieldFinish_ok (hs₀.of_keeps k1 (by decide)) ho
    ((k1.gpr _ (by decide)).trans hz) ((k0.mono (by decide)).trans (k1.mono (by decide))))
    fun t ⟨hop, ht⟩ => ⟨hop, ?_⟩
  rw [ht, e1, k0.mem]
  exact toFe_mul rfl

end VG.Proof.Ed25519.AArch64
