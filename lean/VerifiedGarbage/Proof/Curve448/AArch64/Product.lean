import VerifiedGarbage.Proof.Curve448.AArch64.Columns
import VerifiedGarbage.Proof.Curve448.AArch64.Normalize
namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Proof.X448.AArch64

theorem product_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Impl.Curve448.AArch64.product o a b) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  rw [Impl.Curve448.AArch64.product, List.append_assoc, WP.block_append_iff]
  refine WP.mono (columns_ok hs (Or.inl (by omega)) (Or.inl (by omega))
    (by have := ha; change a + 128 ≤ 3584 at this; omega)
    (by have := hb; change b + 128 ≤ 3584 at this; omega) ha8 hb8 ab bb) fun s₁ ⟨c₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have raw : ∀ i < 16, coeff s₁.mem base ACC i < 2 ^ 116 := by
    intro i hi
    rw [c₁ i hi]
    exact Nat.lt_of_le_of_lt (VG.Proof.Curve448.AArch64.rows_bound ab bb (by decide) i) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.reduce_ok hs₁ raw) fun s₂ ⟨r₂, m₂, k₂⟩ => ?_
  have red := reduced_bound raw
  refine WP.mono (normalize_ok (hs₁.of_keeps k₂ (by decide)) ho ho8 r₂ red) fun t ⟨tf, tm, tk⟩ => ?_
  have val : fe t.mem base o % Spec.X448.P = (fe s.mem base a * fe s.mem base b) % Spec.X448.P := by
    rw [show fe t.mem base o = VG.Proof.X448.Wide.valN
        (folded (folded (reduced (coeff s₁.mem base ACC)))) 8 from
        VG.Proof.X448.Wide.valN_congr tf, twice_mod, reduced_mod,
      VG.Proof.X448.Wide.valN_congr c₁, rows_val f g (by decide)]
  refine ⟨⟨?_, ?_⟩, ?_, VG.Proof.X448.toFe_mul val⟩
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans (tk.mono (by decide)))
  · exact (FieldMem.work m₁ (by decide) (by decide)).trans
      ((FieldMem.work m₂ (by decide) (by decide)).trans tm)
  · intro i hi; rw [tf i hi]; exact twice_weak red i hi
end VG.Proof.Curve448.AArch64
