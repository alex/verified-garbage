import VerifiedGarbage.Proof.Curve448.AArch64.Product
import VerifiedGarbage.Proof.Curve448.AArch64.SymmetricColumns
namespace VG.Proof.Curve448.AArch64
open VG VG.AArch64 VG.Proof.X448.Wide VG.Proof.X448.Wide.Representation
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64

theorem square_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (ab : Bounded s.mem base a) :
    WP isa (Impl.Curve448.AArch64.sqr o a) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base a := by
  let f := limbs s.mem base a
  rw [Impl.Curve448.AArch64.sqr, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadCached_ok hs (by have := ha; change a + 128 ≤ 3584 at this; omega) ha8)
    fun s₁ ⟨c₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have fc : ∀ i < 8, (s₁.gpr (cacheReg i)).toNat = f i := by intro i hi; rw [c₁ i hi]
  rw [WP.block_append_iff]
  refine WP.mono (symmetricColumns_ok hs₁ fc ab) fun s₂ ⟨c₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have raw : ∀ i < 16, coeff s₂.mem base ACC i < 2 ^ 116 := by
    intro i hi; rw [c₂ i hi]
    exact Nat.lt_of_le_of_lt (VG.Proof.Curve448.AArch64.rows_bound ab ab (by decide) i) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Wide.reduce_ok hs₂ raw) fun s₃ ⟨r₃, m₃, k₃⟩ => ?_
  have red := reduced_bound raw
  refine WP.mono (normalize_ok (hs₂.of_keeps k₃ (by decide)) ho ho8 r₃ red) fun t ⟨tf, tm, tk⟩ => ?_
  have val : fe t.mem base o % Spec.X448.P = (fe s.mem base a * fe s.mem base a) % Spec.X448.P := by
    rw [show fe t.mem base o = VG.Proof.X448.Wide.valN
        (folded (folded (reduced (coeff s₂.mem base ACC)))) 8 from
        VG.Proof.X448.Wide.valN_congr tf, twice_mod, reduced_mod,
      VG.Proof.X448.Wide.valN_congr c₂, rows_val f f (by decide)]
  refine ⟨⟨?_, ?_⟩, ?_, VG.Proof.X448.toFe_mul val⟩
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans
      ((k₃.mono (by decide)).trans (tk.mono (by decide))))
  · rw [m₁] at m₂
    exact (FieldMem.work m₂ (by decide) (by decide)).trans
      ((FieldMem.work m₃ (by decide) (by decide)).trans tm)
  · intro i hi; rw [tf i hi]; exact twice_weak red i hi

theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Impl.Curve448.AArch64.mul o a b) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  rw [Impl.Curve448.AArch64.mul]
  by_cases h : a = b
  · rw [ite_eq_left h, ← h]; exact square_ok hs ho ho8 ha ha8 ab
  · rw [ite_eq_right h]; exact product_ok hs ho ho8 ha ha8 hb hb8 ab bb
end VG.Proof.Curve448.AArch64
