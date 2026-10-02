import VerifiedGarbage.Proof.X448.Wide.TailNormalize
import VerifiedGarbage.Proof.X448.Wide.Encoded
import VerifiedGarbage.Proof.X448.AArch64.Mul

/-! Untrusted: wide field multiplication behind the existing X448 slot contract. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC TMP)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64
open VG.Proof.X448 (toFe_mul)

theorem tailProduct_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0)
    (hb : Slot b) (hb8 : b % 8 = 0) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Impl.X448.AArch64.Tail.product o a b) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  let f := paired (limbs s.mem base a)
  let g := paired (limbs s.mem base b)
  have fa : ∀ i < 8, f i < radix := paired_bound ab
  have gb : ∀ i < 8, g i < radix := paired_bound bb
  have aw : a + 128 ≤ 8192 := Nat.le_trans ha (by decide)
  have bw : b + 128 ≤ 8192 := Nat.le_trans hb (by decide)
  rw [Impl.X448.AArch64.Tail.product, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (pack_ok hs (o := PACKA) (by decide) aw (by decide) ha8
    (Or.inl (Nat.le_trans ha (by decide))) ab) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have b₁ : ∀ i < 16, limbs s₁.mem base b i = limbs s.mem base b i :=
    fun i hi => m₁.limbs (Or.inl (Nat.le_trans hb (by decide))) bw hi
  have bb₁ : Bounded s₁.mem base b := by
    intro i hi; rw [b₁ i hi]; exact bb i hi
  rw [WP.block_append_iff]
  refine WP.mono (pack_ok hs₁ (o := PACKB) (by decide) bw (by decide) hb8
    (Or.inl (Nat.le_trans hb (by decide))) bb₁) fun s₂ ⟨b₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have a₂ : ∀ i < 8, limbs s₂.mem base PACKA i = f i := by
    intro i hi
    have eq : limbs s₂.mem base PACKA i = limbs s₁.mem base PACKA i :=
      congrArg BitVec.toNat (m₂.word (by simp only [PACKA, PACKB]; omega) (by simp only [PACKA]; omega))
    rw [eq, a₁ i hi]
  have b₂' : ∀ i < 8, limbs s₂.mem base PACKB i = g i := by
    intro i hi
    rw [b₂ i hi]
    simp only [paired]
    rw [b₁ (2 * i) (by omega), b₁ (2 * i + 1) (by omega)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (columns_ok hs₂ (a := PACKA) (b := PACKB) (Or.inr (by decide))
    (Or.inr (by decide)) (by decide) (by decide) (by decide) (by decide)
    (by intro i hi; rw [a₂ i hi]; exact fa i hi)
    (by intro i hi; rw [b₂' i hi]; exact gb i hi)) fun s₃ ⟨c₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have c₃' : ∀ i < 16, coeff s₃.mem base ACC i = rows f g 8 i := by
    intro i hi
    rw [c₃ i hi]
    exact rows_congr a₂ b₂' (by decide) i
  have raw : ∀ i < 16, coeff s₃.mem base ACC i < 2 ^ 116 := by
    intro i hi
    rw [c₃' i hi]
    exact Nat.lt_of_le_of_lt (rows_bound fa gb (by decide) i) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok hs₃ raw) fun s₄ ⟨r₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have red := reduced_bound raw
  refine WP.mono (tailNormalize_ok hs₄ ho ho8 r₄ red) fun t ⟨tf, tm, tk⟩ => ?_
  have out := encoded_limbs tf
  have val : fe t.mem base o % Spec.X448.P =
      (fe s.mem base a * fe s.mem base b) % Spec.X448.P := by
    rw [show fe t.mem base o = VG.Proof.X448.valN
        (unpacked (normalized (reduced (coeff s₃.mem base ACC)))) 16 from
        VG.Proof.X448.valN_congr out,
      unpacked_val, normalized_mod red, reduced_mod,
      valN_congr c₃', rows_val f g (by decide), paired_val, paired_val]
  refine ⟨⟨?_, ?_⟩, ?_, toFe_mul val⟩
  · exact (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans
      ((k₃.mono (by decide)).trans ((k₄.mono (by decide)).trans (tk.mono (by decide)))))
  · exact (FieldMem.work m₁ (by decide) (by decide)).trans
      ((FieldMem.work m₂ (by decide) (by decide)).trans
      ((FieldMem.work m₃ (by decide) (by decide)).trans
      ((FieldMem.work m₄ (by decide) (by decide)).trans tm)))
  · intro i hi
    rw [out i hi]
    exact unpacked_bound (fun j _ => digit_lt _ j) i hi

end VG.Proof.X448.Wide
