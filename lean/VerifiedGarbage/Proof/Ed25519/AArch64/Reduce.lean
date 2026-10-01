import VerifiedGarbage.Proof.Ed25519.AArch64.Ops
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! Untrusted: reduction of an eight-word field product. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

theorem fold_ok (s : State) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38)
    (hb : (s.gpr .x20).toNat < 2 ^ 52) :
    WP isa (.block fold) s fun t =>
      toFe (val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7)) =
        toFe (val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) + 38 * (s.gpr .x20).toNat) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8] s t := by
  rw [fold, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mul .x .x8 .x20 .x11]) s fun t =>
      (t.gpr .x8).toNat = 38 * (s.gpr .x20).toNat ∧ Keeps [.x8] s t from by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', h38]
    refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
    · rw [BitVec.toNat_mul, show (38 : Word).toNat = 38 from rfl, Nat.mul_comm]
      exact Nat.mod_eq_of_lt (by omega)
    · intro r hr
      exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr))
    fun s₁ ⟨e1, k1⟩ => ?_
  have hz1 := (k1.gpr .x10 (by decide)).trans hz
  have h381 := (k1.gpr .x11 (by decide)).trans h38
  have hx : (s₁.gpr .x8).toNat < 2 ^ 58 := by rw [e1]; omega
  refine WP.mono (carry38_ok s₁ hz1 h381 hx) fun s₂ ⟨e2, k2⟩ => ?_
  refine ⟨?_, (k1.mono (by decide)).trans k2⟩
  rw [e2, e1, k1.gpr .x4 (by decide), k1.gpr .x5 (by decide),
    k1.gpr .x6 (by decide), k1.gpr .x7 (by decide)]

/-- The eight words of a full product: x4–x7, then x21–x24. -/
abbrev wide (s : State) : Nat :=
  val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) +
    2 ^ 256 * val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)

theorem movz38_ok (s : State) :
    WP isa (.block [.movz .w .x11 38 0]) s fun t => t.gpr .x11 = 38 ∧ Keeps [.x11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun q hq => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hq)

/-- `reduceWide`: the eight words of a product, reduced modulo p into x4–x7. -/
theorem reduceWide_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block reduceWide) s fun t =>
      toFe (val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7)) = toFe (wide s) ∧
      t.gpr .x10 = 0 ∧
      Keeps [.x2, .x8, .x9, .x11, .x16, .x4, .x5, .x6, .x7, .x20] s t := by
  rw [reduceWide, List.append_assoc, WP.block_append_iff]
  refine WP.mono (movz38_ok s) fun s₁ ⟨h38, k1⟩ => ?_
  have hz1 : s₁.gpr .x10 = 0 := (k1.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (rowAccReduce_ok s₁ hz1) fun s₂ ⟨e2, k2⟩ => ?_
  have hz2 : s₂.gpr .x10 = 0 := (k2.gpr _ (by decide)).trans hz1
  have h382 : s₂.gpr .x11 = 38 := (k2.gpr _ (by decide)).trans h38
  have hc : (s₂.gpr .x20).toNat < 2 ^ 52 := by
    have hl := val4_lt (s₁.gpr .x4) (s₁.gpr .x5) (s₁.gpr .x6) (s₁.gpr .x7)
    have hh := val4_lt (s₁.gpr .x21) (s₁.gpr .x22) (s₁.gpr .x23) (s₁.gpr .x24)
    rw [h38, show (38 : Word).toNat = 38 from rfl] at e2
    omega_using [e2, hl, hh]
  refine WP.mono (fold_ok s₂ hz2 h382 hc) fun s₃ ⟨e3, k3⟩ => ?_
  refine ⟨?_, (k3.gpr _ (by decide)).trans hz2,
    ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))⟩
  rw [e3]
  rw [h38, show (38 : Word).toNat = 38 from rfl, k1.gpr .x4 (by decide), k1.gpr .x5 (by decide),
    k1.gpr .x6 (by decide), k1.gpr .x7 (by decide), k1.gpr .x21 (by decide),
    k1.gpr .x22 (by decide), k1.gpr .x23 (by decide), k1.gpr .x24 (by decide)] at e2
  apply toFe_congr
  rw [← fold256, e2, fold256]

end VG.Proof.Ed25519.AArch64
