import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Ed25519.AArch64.Mul
import Mathlib.Tactic.Ring

/-! Four-word field squaring. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

theorem sq_expand_radix (R A0 A1 A2 A3 : Nat) :
    (A0 + R * A1 + R * R * A2 + R * R * R * A3) * (A0 + R * A1 + R * R * A2 + R * R * R * A3) =
      R * (2 * (A0 * A1 + R * (A0 * A2) + R * R * (A0 * A3 + A1 * A2) + R * R * R * (A1 * A3) +
        R * R * R * R * (A2 * A3))) +
        (A0 * A0 + R * R * (A1 * A1) + R * R * R * R * (A2 * A2 + R * R * (A3 * A3))) := by
  ring

/-- The square of four words: twice the products of distinct words, and the squares. -/
theorem sq_expand (A0 A1 A2 A3 : Nat) :
    (A0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3) *
        (A0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3) =
      2 ^ 64 * (2 * cross A0 A1 A2 A3) + diag A0 A1 A2 A3 := by
  have h := sq_expand_radix (2 ^ 64) A0 A1 A2 A3
  rw [show (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 from rfl,
    show (2 : Nat) ^ 128 * 2 ^ 64 = 2 ^ 192 from rfl,
    show (2 : Nat) ^ 192 * 2 ^ 64 = 2 ^ 256 from rfl] at h
  exact h

theorem sqrWide_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat}
    (ha : FieldRange a) (hz : s.gpr .x10 = 0) :
    WP isa (.block (sqrWide a)) s fun t =>
      wide t = fe s.mem base a * fe s.mem base a ∧
      Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
        .x21, .x22, .x23, .x24] s t := by
  simp only [sqrWide, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs ha (by decide)) fun s₁ ⟨a0, a1, a2, a3, k1⟩ => ?_
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (sqrCross_ok s₁ hz1) fun s₂ ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sqrDouble_ok s₂ ((k2.gpr _ (by decide)).trans hz1)) fun s₃ ⟨e3, k3⟩ => ?_
  refine WP.mono (sqrDiag_ok s₃) fun s₄ ⟨c, e4, k4⟩ => ?_
  refine ⟨?_, (((k1.mono (by decide)).trans (k2.mono (by decide))).trans
    (k3.mono (by decide))).trans (k4.mono (by decide))⟩
  have A : ∀ (r : Reg), r ∈ [.x12, .x13, .x14, .x15] → s₃.gpr r = s₁.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (k3.gpr _ (by decide)).trans (k2.gpr _ (by decide))
  rw [A .x12 (by decide), A .x13 (by decide), A .x14 (by decide), A .x15 (by decide),
    e3, e2, a0, a1, a2, a3] at e4
  have hlt : fe s.mem base a * fe s.mem base a < 2 ^ 256 * 2 ^ 256 :=
    Nat.mul_lt_mul'' (val4_lt _ _ _ _) (val4_lt _ _ _ _)
  have hx := sq_expand (word s.mem base a).toNat (word s.mem base (a + 8)).toNat
    (word s.mem base (a + 16)).toNat (word s.mem base (a + 24)).toNat
  dsimp only [wide]
  rw [show fe s.mem base a * fe s.mem base a = _ from hx]
  rw [show fe s.mem base a * fe s.mem base a = _ from hx] at hlt
  omega_using [e4, hlt]

/-- Squaring modulo p, allowing the output to alias the input. -/
theorem sqr_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : FieldRange o) (ha : FieldRange a) :
    WP isa (.block (fieldSqr o a)) s fun t =>
      Op base o s t ∧ F t.mem base o = F s.mem base a * F s.mem base a := by
  rw [fieldSqr, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zeroReg_ok s .x10) fun s₀ ⟨hz, k0⟩ => ?_
  have hs₀ := hs.of_keeps k0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqrWide_ok hs₀ ha hz) fun s₁ ⟨e1, k1⟩ => ?_
  refine WP.mono (fieldFinish_ok (hs₀.of_keeps k1 (by decide)) ho
    ((k1.gpr _ (by decide)).trans hz) ((k0.mono (by decide)).trans (k1.mono (by decide))))
    fun t ⟨hop, ht⟩ => ⟨hop, ?_⟩
  rw [ht, e1, k0.mem]
  exact toFe_mul rfl

end VG.Proof.Ed25519.AArch64
