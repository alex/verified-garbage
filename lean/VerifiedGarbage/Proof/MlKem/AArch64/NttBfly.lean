import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon

/-!
# ML-KEM on AArch64: the butterflies of the NTT and its inverse

Untrusted: everything here is checked by Lean. One butterfly (`bflyBody`,
`ibflyBody`) on the coefficients `j` and `j + len` at `x2` and `x3`, with
the zeta in `x17`, as `bfly` and `bflyInv` (`Proof/MlKem/Ntt.lean`) of the
polynomial in memory.
-/

namespace VG.Proof.MlKem.AArch64.Ntt

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem

/-- What a butterfly leaves. -/
structure BflyPost (s₀ : State) (f : Poly → Poly) (j len : Nat) (P : Poly) (t t' : State) : Prop where
  st : St s₀ t'
  keep : Keep [.x2, .x3, .x4, .x5, .x6, .x7, .x8] t t'
  x2 : t'.gpr .x2 = fP s₀ + BitVec.ofNat 64 (4 * (j + 1))
  x3 : t'.gpr .x3 = fP s₀ + BitVec.ofNat 64 (4 * (j + len + 1))
  x5 : t'.gpr .x5 = t.gpr .x5 - BitVec.ofNat 64 1
  poly : PolyIs t'.mem (fP s₀) (f P)

theorem bfly_step {s₀ : State} (hp : Pre s₀) {P : Poly} {Z : Zq} {j len : Nat} (hlen : 0 < len)
    (hj : j + len < 256) {t : State} (h : St s₀ t) (h2 : t.gpr .x2 = fP s₀ + BitVec.ofNat 64 (4 * j))
    (h3 : t.gpr .x3 = fP s₀ + BitVec.ofNat 64 (4 * (j + len))) (h17 : (t.gpr .x17).toNat = Z.val)
    (hP : PolyIs t.mem (fP s₀) P) :
    WP isa (.block bflyBody) t (BflyPost s₀ (fun P => bfly P j len Z) j len P t) := by
  have hq : q = 3329 := rfl
  have la := val_lt P[j]!
  have lb := val_lt P[j + len]!
  have lz := val_lt Z
  refine wp_ldrw (a := coeffAddr (fP s₀) j) (by decide) (by rw [h2, ptr_zero]) (hp.in_f' h (by omega))
    fun t₁ h₁ e₁ => ?_
  refine wp_ldrw (a := coeffAddr (fP s₀) (j + len)) (by decide) (by rw [h₁.get .x3, h3, ptr_zero])
    (by rw [h₁.rd, h₁.wr]; exact hp.in_f' h (by omega)) fun t₂ h₂ e₂ => ?_
  have v6 : (t₂.gpr .x6).toNat = (P[j]!).val := by
    rw [h₂.get .x6, e₁, toNat_readW32, ← coeffAt_eq, polyIs_toNat hP (show j < n by rw [n_eq]; omega)]
  have v7 : (t₂.gpr .x7).toNat = (P[j + len]!).val := by
    rw [e₂, toNat_readW32, h₁.mem, ← coeffAt_eq, polyIs_toNat hP (show j + len < n by rw [n_eq]; omega)]
  have k₂ := h₁.keep.trans h₂.keep
  refine wp_mul fun t₃ h₃ e₃ => ?_
  have p₁ := mul_lt_q2 lb lz
  have v₃ : (t₃.gpr .x7).toNat = (P[j + len]!).val * Z.val := by
    have hb : (t₂.gpr .x7).toNat * (t₂.gpr .x17).toNat < 2 ^ 64 := by
      rw [v7, k₂.get .x17, h17]; omega
    rw [e₃, toNat_mul_n hb, v7, k₂.get .x17, h17]
  have k₃ := k₂.trans h₃.keep
  refine reduce_ok (by decide) (by decide) (by decide) (by omega) v₃ (by rw [k₃.get .x10, h.x10])
    (by rw [k₃.get .x9, h.x9]) fun t₄ h₄ e₄ => ?_
  -- t = Z · P[j + len]
  have et : (P[j + len]!).val * Z.val % q = (Z * P[j + len]!).val := by rw [val_mul, Nat.mul_comm]
  rw [et] at e₄
  have lt := val_lt (Z * P[j + len]!)
  have k₄ := k₃.trans h₄.keep
  refine wp_add fun t₅ h₅ e₅ => ?_
  have v₅ : (t₅.gpr .x8).toNat = (P[j]!).val + (Z * P[j + len]!).val := by
    rw [e₅, toNat_add_n (by rw [h₄.get .x6, h₃.get .x6, v6, e₄]; omega), h₄.get .x6, h₃.get .x6, v6, e₄]
  have k₅ := k₄.trans h₅.keep
  refine csub_ok (by decide) (by decide) (by decide) (by omega) v₅ (by rw [k₅.get .x9, h.x9])
    fun t₆ h₆ e₆ => ?_
  rw [← val_add] at e₆
  have k₆ := k₅.trans h₆.keep
  refine wp_strw (a := coeffAddr (fP s₀) j) (by decide) (by rw [k₆.get .x2, h2, ptr_zero])
    (by rw [k₆.wr]; exact hp.in_f h (by omega)) fun t₇ h₇ => ?_
  refine wp_add fun t₈ h₈ e₈ => wp_sub fun t₉ h₉ e₉ => ?_
  have c6 : (t₇.gpr .x6).toNat = (P[j]!).val := by
    rw [h₇.gpr, h₆.get .x6, h₅.get .x6, h₄.get .x6, h₃.get .x6, v6]
  have c9 : (t₇.gpr .x9).toNat = q := by rw [h₇.gpr, k₆.get .x9, h.x9]
  have c₈ : (t₈.gpr .x6).toNat = (P[j]!).val + q := by
    have hb : (t₇.gpr .x6).toNat + (t₇.gpr .x9).toNat < 2 ^ 64 := by rw [c6, c9]; omega
    rw [e₈, toNat_add_n hb, c6, c9]
  have c7 : (t₈.gpr .x7).toNat = (Z * P[j + len]!).val := by
    rw [h₈.get .x7, h₇.gpr, h₆.get .x7, h₅.get .x7, e₄]
  have v₉ : (t₉.gpr .x6).toNat = (P[j]!).val + q - (Z * P[j + len]!).val := by
    have hb : (t₈.gpr .x7).toNat ≤ (t₈.gpr .x6).toNat := by rw [c₈, c7]; omega
    rw [e₉, toNat_sub_n hb, c₈, c7]
  have k₉ := ((k₆.trans h₇.keep).trans h₈.keep).trans h₉.keep
  refine csub_ok (by decide) (by decide) (by decide) (by omega) v₉ (by rw [k₉.get .x9, h.x9])
    fun t₁₀ h₁₀ e₁₀ => ?_
  rw [← val_sub] at e₁₀
  have k₁₀ := k₉.trans h₁₀.keep
  refine wp_strw (a := coeffAddr (fP s₀) (j + len)) (by decide) (by rw [k₁₀.get .x3, h3, ptr_zero])
    (by rw [k₁₀.wr]; exact hp.in_f h (by omega)) fun t₁₁ h₁₁ => ?_
  refine wp_addImm (by decide) fun t₁₂ h₁₂ e₁₂ => wp_addImm (by decide) fun t₁₃ h₁₃ e₁₃ =>
    wp_subImm (by decide) fun t₁₄ h₁₄ e₁₄ => wp_nil ?_
  have k₁₁ := k₁₀.trans h₁₁.keep
  have k₁₄ := ((k₁₁.trans h₁₂.keep).trans h₁₃.keep).trans h₁₄.keep
  have m₁₄ : t₁₄.mem = (t.mem.writeW (coeffAddr (fP s₀) j)
      (BitVec.ofNat 32 (P[j]! + Z * P[j + len]!).val)).writeW (coeffAddr (fP s₀) (j + len))
      (BitVec.ofNat 32 (P[j]! - Z * P[j + len]!).val) := by
    rw [h₁₄.mem, h₁₃.mem, h₁₂.mem, h₁₁.mem, h₁₀.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem,
      h₄.mem, h₃.mem, h₂.mem, h₁.mem, setWidth32_of_toNat e₆, setWidth32_of_toNat e₁₀]
  have fr : Frame [polyRegion (fP s₀)] t.mem t₁₄.mem := by
    rw [m₁₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (coeff_contains _ (show j < n by rw [n_eq]; omega))).writeW (List.mem_singleton_self _) _
      (coeff_contains _ (show j + len < n by rw [n_eq]; omega))
  refine ⟨⟨by rw [k₁₄.rd, h.rd], by rw [k₁₄.wr, h.wr], by rw [k₁₄.sp, h.sp], by rw [k₁₄.get .x0, h.x0],
    by rw [k₁₄.get .x9, h.x9], by rw [k₁₄.get .x10, h.x10], hp.tab_write fr h.tab⟩, k₁₄.mono, ?_, ?_,
    ?_, ?_⟩
  · rw [h₁₄.get .x2, h₁₃.get .x2, e₁₂, k₁₁.get .x2, h2, ptr_next]
  · rw [h₁₄.get .x3, e₁₃, h₁₂.get .x3, k₁₁.get .x3, h3, ptr_next]
  · rw [e₁₄, h₁₃.get .x5, h₁₂.get .x5, k₁₁.get .x5]
  · rw [m₁₄]
    refine polyIs_write2 hP (by omega) (by omega) (by omega) fun i hi => ?_
    rw [bfly_get _ hlen (show j + len < n by rw [n_eq]; omega) _ (show i < n from hi)]

theorem ibfly_step {s₀ : State} (hp : Pre s₀) {P : Poly} {Z : Zq} {j len : Nat} (hlen : 0 < len)
    (hj : j + len < 256) {t : State} (h : St s₀ t) (h2 : t.gpr .x2 = fP s₀ + BitVec.ofNat 64 (4 * j))
    (h3 : t.gpr .x3 = fP s₀ + BitVec.ofNat 64 (4 * (j + len))) (h17 : (t.gpr .x17).toNat = Z.val)
    (hP : PolyIs t.mem (fP s₀) P) :
    WP isa (.block ibflyBody) t (BflyPost s₀ (fun P => bflyInv P j len Z) j len P t) := by
  have hq : q = 3329 := rfl
  have la := val_lt P[j]!
  have lb := val_lt P[j + len]!
  have lz := val_lt Z
  refine wp_ldrw (a := coeffAddr (fP s₀) j) (by decide) (by rw [h2, ptr_zero]) (hp.in_f' h (by omega))
    fun t₁ h₁ e₁ => ?_
  refine wp_ldrw (a := coeffAddr (fP s₀) (j + len)) (by decide) (by rw [h₁.get .x3, h3, ptr_zero])
    (by rw [h₁.rd, h₁.wr]; exact hp.in_f' h (by omega)) fun t₂ h₂ e₂ => ?_
  have v6 : (t₂.gpr .x6).toNat = (P[j]!).val := by
    rw [h₂.get .x6, e₁, toNat_readW32, ← coeffAt_eq, polyIs_toNat hP (show j < n by rw [n_eq]; omega)]
  have v7 : (t₂.gpr .x7).toNat = (P[j + len]!).val := by
    rw [e₂, toNat_readW32, h₁.mem, ← coeffAt_eq, polyIs_toNat hP (show j + len < n by rw [n_eq]; omega)]
  have k₂ := h₁.keep.trans h₂.keep
  refine wp_add fun t₃ h₃ e₃ => ?_
  have v₃ : (t₃.gpr .x8).toNat = (P[j]!).val + (P[j + len]!).val := by
    have hb : (t₂.gpr .x6).toNat + (t₂.gpr .x7).toNat < 2 ^ 64 := by rw [v6, v7]; omega
    rw [e₃, toNat_add_n hb, v6, v7]
  have k₃ := k₂.trans h₃.keep
  refine csub_ok (by decide) (by decide) (by decide) (by omega) v₃ (by rw [k₃.get .x9, h.x9])
    fun t₄ h₄ e₄ => ?_
  rw [← val_add] at e₄
  have k₄ := k₃.trans h₄.keep
  refine wp_strw (a := coeffAddr (fP s₀) j) (by decide) (by rw [k₄.get .x2, h2, ptr_zero])
    (by rw [k₄.wr]; exact hp.in_f h (by omega)) fun t₅ h₅ => ?_
  refine wp_add fun t₆ h₆ e₆ => wp_sub fun t₇ h₇ e₇ => ?_
  have c7 : (t₅.gpr .x7).toNat = (P[j + len]!).val := by rw [h₅.gpr, h₄.get .x7, h₃.get .x7, v7]
  have c9 : (t₅.gpr .x9).toNat = q := by rw [h₅.gpr, k₄.get .x9, h.x9]
  have c₆ : (t₆.gpr .x7).toNat = (P[j + len]!).val + q := by
    have hb : (t₅.gpr .x7).toNat + (t₅.gpr .x9).toNat < 2 ^ 64 := by rw [c7, c9]; omega
    rw [e₆, toNat_add_n hb, c7, c9]
  have c6 : (t₆.gpr .x6).toNat = (P[j]!).val := by
    rw [h₆.get .x6, h₅.gpr, h₄.get .x6, h₃.get .x6, v6]
  have v₇ : (t₇.gpr .x7).toNat = (P[j + len]!).val + q - (P[j]!).val := by
    have hb : (t₆.gpr .x6).toNat ≤ (t₆.gpr .x7).toNat := by rw [c₆, c6]; omega
    rw [e₇, toNat_sub_n hb, c₆, c6]
  have k₇ := ((k₄.trans h₅.keep).trans h₆.keep).trans h₇.keep
  refine csub_ok (by decide) (by decide) (by decide) (by omega) v₇ (by rw [k₇.get .x9, h.x9])
    fun t₈ h₈ e₈ => ?_
  rw [← val_sub] at e₈
  have k₈ := k₇.trans h₈.keep
  refine wp_mul fun t₉ h₉ e₉ => ?_
  have ld := val_lt (P[j + len]! - P[j]!)
  have p₁ := mul_lt_q2 ld lz
  have v₉ : (t₉.gpr .x7).toNat = (P[j + len]! - P[j]!).val * Z.val := by
    have hb : (t₈.gpr .x7).toNat * (t₈.gpr .x17).toNat < 2 ^ 64 := by
      rw [e₈, k₈.get .x17, h17]; omega
    rw [e₉, toNat_mul_n hb, e₈, k₈.get .x17, h17]
  have k₉ := k₈.trans h₉.keep
  refine reduce_ok (by decide) (by decide) (by decide) (by omega) v₉ (by rw [k₉.get .x10, h.x10])
    (by rw [k₉.get .x9, h.x9]) fun t₁₀ h₁₀ e₁₀ => ?_
  have et : (P[j + len]! - P[j]!).val * Z.val % q = (Z * (P[j + len]! - P[j]!)).val := by
    rw [val_mul, Nat.mul_comm]
  rw [et] at e₁₀
  have k₁₀ := k₉.trans h₁₀.keep
  refine wp_strw (a := coeffAddr (fP s₀) (j + len)) (by decide) (by rw [k₁₀.get .x3, h3, ptr_zero])
    (by rw [k₁₀.wr]; exact hp.in_f h (by omega)) fun t₁₁ h₁₁ => ?_
  refine wp_addImm (by decide) fun t₁₂ h₁₂ e₁₂ => wp_addImm (by decide) fun t₁₃ h₁₃ e₁₃ =>
    wp_subImm (by decide) fun t₁₄ h₁₄ e₁₄ => wp_nil ?_
  have k₁₁ := k₁₀.trans h₁₁.keep
  have k₁₄ := ((k₁₁.trans h₁₂.keep).trans h₁₃.keep).trans h₁₄.keep
  have m₁₄ : t₁₄.mem = (t.mem.writeW (coeffAddr (fP s₀) j)
      (BitVec.ofNat 32 (P[j]! + P[j + len]!).val)).writeW (coeffAddr (fP s₀) (j + len))
      (BitVec.ofNat 32 (Z * (P[j + len]! - P[j]!)).val) := by
    rw [h₁₄.mem, h₁₃.mem, h₁₂.mem, h₁₁.mem, h₁₀.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem,
      h₄.mem, h₃.mem, h₂.mem, h₁.mem, setWidth32_of_toNat e₄, setWidth32_of_toNat e₁₀]
  have fr : Frame [polyRegion (fP s₀)] t.mem t₁₄.mem := by
    rw [m₁₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (coeff_contains _ (show j < n by rw [n_eq]; omega))).writeW (List.mem_singleton_self _) _
      (coeff_contains _ (show j + len < n by rw [n_eq]; omega))
  refine ⟨⟨by rw [k₁₄.rd, h.rd], by rw [k₁₄.wr, h.wr], by rw [k₁₄.sp, h.sp], by rw [k₁₄.get .x0, h.x0],
    by rw [k₁₄.get .x9, h.x9], by rw [k₁₄.get .x10, h.x10], hp.tab_write fr h.tab⟩, k₁₄.mono, ?_, ?_,
    ?_, ?_⟩
  · rw [h₁₄.get .x2, h₁₃.get .x2, e₁₂, k₁₁.get .x2, h2, ptr_next]
  · rw [h₁₄.get .x3, e₁₃, h₁₂.get .x3, k₁₁.get .x3, h3, ptr_next]
  · rw [e₁₄, h₁₃.get .x5, h₁₂.get .x5, k₁₁.get .x5]
  · rw [m₁₄]
    refine polyIs_write2 hP (by omega) (by omega) (by omega) fun i hi => ?_
    rw [bflyInv_get _ hlen (show j + len < n by rw [n_eq]; omega) _ (show i < n from hi)]

end VG.Proof.MlKem.AArch64.Ntt
