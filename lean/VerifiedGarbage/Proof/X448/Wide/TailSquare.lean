import VerifiedGarbage.Proof.X448.Wide.TailProduct
import VerifiedGarbage.Proof.X448.Wide.SymmetricColumns
import VerifiedGarbage.Proof.X448.Wide.Mul

/-! Untrusted: cached-input squaring behind the unchanged field-slot contract. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Cached VG.Proof.X448.AArch64
open VG.Proof.X448 (toFe_mul)

theorem tailSquare_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0) (ab : Bounded s.mem base a) :
    WP isa (Impl.X448.AArch64.Tail.sqr o a) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base a := by
  let f := paired (limbs s.mem base a)
  have fb : ∀ i < 8, f i < radix := paired_bound ab
  rw [Impl.X448.AArch64.Tail.sqr, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (pack_ok hs (o := Impl.X448.AArch64.Wide.PACKA) (by decide)
    (Nat.le_trans ha (by decide)) (by decide) ha8 (Or.inl (Nat.le_trans ha (by decide))) ab)
    fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadCached_ok hs₁ (a := Impl.X448.AArch64.Wide.PACKA) (by decide) (by decide))
    fun s₂ ⟨c₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have fc : ∀ i < 8, (s₂.gpr (cacheReg i)).toNat = f i := by
    intro i hi
    rw [c₂ i hi]
    exact a₁ i hi
  rw [WP.block_append_iff]
  refine WP.mono (symmetricColumns_ok hs₂ fc fb) fun s₃ ⟨c₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have raw : ∀ i < 16, coeff s₃.mem base ACC i < 2 ^ 116 := by
    intro i hi
    rw [c₃ i hi]
    exact Nat.lt_of_le_of_lt (rows_bound fb fb (by decide) i) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok hs₃ raw) fun s₄ ⟨r₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have red := reduced_bound raw
  refine WP.mono (tailNormalize_ok hs₄ ho ho8 r₄ red) fun t ⟨tf, tm, tk⟩ => ?_
  have out := encoded_limbs tf
  have val : fe t.mem base o % Spec.X448.P =
      (fe s.mem base a * fe s.mem base a) % Spec.X448.P := by
    rw [show fe t.mem base o = VG.Proof.X448.valN
        (unpacked (normalized (reduced (coeff s₃.mem base ACC)))) 16 from
        VG.Proof.X448.valN_congr out,
      unpacked_val, normalized_mod red, reduced_mod,
      valN_congr c₃, rows_val f f (by decide), paired_val]
  refine ⟨⟨?_, ?_⟩, ?_, toFe_mul val⟩
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans
      ((k₃.mono (by decide)).trans ((k₄.mono (by decide)).trans (tk.mono (by decide)))))
  · rw [m₂] at m₃
    exact (FieldMem.work m₁ (by decide) (by decide)).trans
      ((FieldMem.work m₃ (by decide) (by decide)).trans
      ((FieldMem.work m₄ (by decide) (by decide)).trans tm))
  · intro i hi
    rw [out i hi]
    exact unpacked_bound (fun j _ => digit_lt _ j) i hi

end VG.Proof.X448.Wide
