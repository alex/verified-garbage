import VerifiedGarbage.Proof.Ed25519.AArch64.Row
import VerifiedGarbage.Proof.Ed25519.AArch64.Reduce

/-! Untrusted: four-by-four word field multiplication and its memory frame. -/
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

theorem wideProduct_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : FieldRange a) (hb : FieldRange b) (hz : s.gpr .x10 = 0) :
    WP isa (.block (wideProduct a b)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) +
        2 ^ 256 * val4 (t.gpr .x21) (t.gpr .x22) (t.gpr .x23) (t.gpr .x24) =
          fe s.mem base a * fe s.mem base b ∧ Keeps wideClob s t := by
  rw [show wideProduct a b = zero4 ++
      (row a b 0 ++ (row a b 1 ++ (row a b 2 ++ row a b 3))) by
    simp only [wideProduct, List.append_assoc], WP.block_append_iff]
  refine WP.mono (zero4_ok s) fun s₀ ⟨z4, z5, z6, z7, k0⟩ => ?_
  refine WP.mono (rowsAccumulate_ok (hs.of_keeps k0 (by decide)) ha hb
    ((k0.gpr .x10 (by decide)).trans hz)) fun t ⟨hv, kt⟩ => ?_
  refine ⟨?_, (k0.mono (by decide)).trans kt⟩
  have hz : (0 : Word).toNat = 0 := rfl
  simpa only [z4, z5, z6, z7, val4, hz, Nat.mul_zero,
    Nat.zero_add, k0.mem] using hv

theorem mul_mod_arith {L H V c AB : Nat} (h₁ : V + 2 ^ 256 * c = L + 38 * H)
    (h₂ : L + 2 ^ 256 * H = AB) : (V + 38 * c) % Spec.X25519.P = AB % Spec.X25519.P := by
  rw [← h₂, fold256, ← h₁, fold256]

/-- Multiplication modulo p, allowing the output to alias either input. -/
theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : FieldRange o) (ha : FieldRange a) (hb : FieldRange b) :
    WP isa (.block (fieldMul o a b)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  rw [fieldMul, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldInit_ok s) fun s₀ ⟨hz, h38, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wideProduct_ok hs₀ ha hb hz) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs₀.of_keeps k1 (by decide)
  have hz1 := (k1.gpr .x10 (by decide)).trans hz
  have h381 := (k1.gpr .x11 (by decide)).trans h38
  rw [show reduce ++ store4 o = (([.movz .w .x3 38 0, .movz .w .x20 0 0] : List Instr) ++
      (mulStep .x4 .x20 .x3 .x21 ++ (mulStep .x5 .x20 .x3 .x22 ++
        (mulStep .x6 .x20 .x3 .x23 ++ mulStep .x7 .x20 .x3 .x24)))) ++
      (fold ++ store4 o) by simp only [reduce_eq, List.append_assoc], WP.block_append_iff]
  refine WP.mono (reduceSteps_ok s₁ hz1) fun s₂ ⟨e2, _, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  have hz2 := (k2.gpr .x10 (by decide)).trans hz1
  have h382 := (k2.gpr .x11 (by decide)).trans h381
  have hc : (s₂.gpr .x20).toNat < 2 ^ 52 := by
    have hl := val4_lt (s₁.gpr .x4) (s₁.gpr .x5) (s₁.gpr .x6) (s₁.gpr .x7)
    have hh := val4_lt (s₁.gpr .x21) (s₁.gpr .x22) (s₁.gpr .x23) (s₁.gpr .x24)
    omega_using [e2, hl, hh]
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok s₂ hz2 h382 hc) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  refine WP.mono (store4_ok hs₃ ho) fun s₄ heq => ?_
  subst s₄
  have K : Keeps clob s s₃ :=
    ((k0.mono (by decide)).trans (k1.mono (by decide))).trans (k2.mono (by decide)) |>.trans
      (k3.mono (by decide))
  refine ⟨Op.of_store ho K _ _ _ _, ?_⟩
  simp only [F]
  rw [fe_st4 _ _ (by have := ho.2; omega), e3]
  rw [k0.mem] at e1
  exact (toFe_congr (mul_mod_arith e2 e1)).trans (toFe_mul rfl)

end VG.Proof.Ed25519.AArch64
