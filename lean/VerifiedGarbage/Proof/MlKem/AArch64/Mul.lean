import VerifiedGarbage.Proof.MlKem.AArch64.Barrett

/-!
# ML-KEM on AArch64: `vg_mlkem_multiply_ntts`

Untrusted: everything here is checked by Lean. One pair of coefficients per
iteration (`multiplyNTTs_even`, `multiplyNTTs_odd`), with the `γᵢ` read from
the table in `scratch`.
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem

/-- The contract the proof is written against (and verified callers use);
the artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for `vg_mlkem_multiply_ntts(h = x0, f = x1, g = x2,
scratch = x3)`: if the polynomials at `f` and `g` are reduced, writes
`MultiplyNTTs(f, g)` to `h`, reduced. The code may read `f` and `g` (which
may overlap) and read and write `h` and `scratch` (1024 bytes), which
overlap nothing. -/
def mulAArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 1024⟩, ⟨s.gpr .x2, 1024⟩] ∧ s.wr = [⟨s.gpr .x0, 1024⟩, ⟨s.gpr .x3, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x1, 1024⟩ ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x2, 1024⟩ ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x3, 1024⟩ ∧
    Region.Disjoint ⟨s.gpr .x1, 1024⟩ ⟨s.gpr .x3, 1024⟩ ∧
    Region.Disjoint ⟨s.gpr .x2, 1024⟩ ⟨s.gpr .x3, 1024⟩ ∧
    Reduced s.mem (s.gpr .x1) ∧ Reduced s.mem (s.gpr .x2)
  post s s' :=
    PolyIs s'.mem (s.gpr .x0) (multiplyNTTs (polyAt s.mem (s.gpr .x1)) (polyAt s.mem (s.gpr .x2)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Mul

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem

theorem even_val (A B C D Γ : Zq) :
    (A * B + C * D * Γ).val = ((C.val * D.val % q) * Γ.val + A.val * B.val) % q := by
  rw [val_add', val_mul, val_mul, val_mul]
  generalize A.val * B.val = P
  generalize C.val * D.val % q * Γ.val = R
  rw [q_eq]
  omega

theorem odd_val (A B C D : Zq) : (A * D + C * B).val = (A.val * D.val + C.val * B.val) % q := by
  rw [val_add', val_mul, val_mul]
  generalize A.val * D.val = P
  generalize C.val * B.val = R
  rw [q_eq]
  omega

section
variable (s₀ : State)

abbrev hP : Addr := s₀.gpr .x0
abbrev fP : Addr := s₀.gpr .x1
abbrev gP : Addr := s₀.gpr .x2
abbrev sP : Addr := s₀.gpr .x3
abbrev F : Poly := polyAt s₀.mem (fP s₀)
abbrev Gp : Poly := polyAt s₀.mem (gP s₀)
/-- Coefficient `j` of the output. -/
def G (j : Nat) : BitVec 32 := BitVec.ofNat 32 ((multiplyNTTs (F s₀) (Gp s₀))[j]!).val
def old (j : Nat) : BitVec 32 := coeffAt s₀.mem (hP s₀) j

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [polyRegion (fP s₀), polyRegion (gP s₀)]
  wr : s₀.wr = [polyRegion (hP s₀), polyRegion (sP s₀)]
  hf : (polyRegion (hP s₀)).Disjoint (polyRegion (fP s₀))
  hg : (polyRegion (hP s₀)).Disjoint (polyRegion (gP s₀))
  hs : (polyRegion (hP s₀)).Disjoint (polyRegion (sP s₀))
  fs : (polyRegion (fP s₀)).Disjoint (polyRegion (sP s₀))
  gs : (polyRegion (gP s₀)).Disjoint (polyRegion (sP s₀))
  f : Reduced s₀.mem (fP s₀)
  g : Reduced s₀.mem (gP s₀)

/-- After `i` pairs. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = hP s₀ + BitVec.ofNat 64 (8 * i)
  x1 : s.gpr .x1 = fP s₀ + BitVec.ofNat 64 (8 * i)
  x2 : s.gpr .x2 = gP s₀ + BitVec.ofNat 64 (8 * i)
  x3 : s.gpr .x3 = sP s₀ + BitVec.ofNat 64 (4 * i)
  x9 : (s.gpr .x9).toNat = q
  x10 : (s.gpr .x10).toNat = 1290167
  x11 : (s.gpr .x11).toNat = 128 - i
  out : CoeffsUpTo s.mem (hP s₀) (2 * i) (G s₀) (old s₀)
  f : ∀ j < 256, coeffAt s.mem (fP s₀) j = coeffAt s₀.mem (fP s₀) j
  g : ∀ j < 256, coeffAt s.mem (gP s₀) j = coeffAt s₀.mem (gP s₀) j
  tab : ∀ j < 128, s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (gammaTable.getD j 0)

theorem G_even (s₀ : State) {i : Nat} (hi : i < 128) :
    G s₀ (2 * i) = BitVec.ofNat 32 ((((F s₀)[2 * i + 1]!).val * ((Gp s₀)[2 * i + 1]!).val % q *
      gammaTable.getD i 0 + ((F s₀)[2 * i]!).val * ((Gp s₀)[2 * i]!).val) % q) := by
  rw [G, multiplyNTTs_even _ _ hi, even_val, gammaTable_eq, gammas_getD hi]

theorem G_odd (s₀ : State) {i : Nat} (hi : i < 128) :
    G s₀ (2 * i + 1) = BitVec.ofNat 32 ((((F s₀)[2 * i]!).val * ((Gp s₀)[2 * i + 1]!).val +
      ((F s₀)[2 * i + 1]!).val * ((Gp s₀)[2 * i]!).val) % q) := by
  rw [G, multiplyNTTs_odd _ _ hi, odd_val]

theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 128) {s : State} (h : Inv s₀ i s) :
    WP isa (.block mulBody) s fun s' => Inv s₀ (i + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ i + 1 ≠ 128) := by
  have hq : q = 3329 := rfl
  have c0 : s.gpr .x1 + BitVec.ofNat 64 0 = coeffAddr (fP s₀) (2 * i) := by
    rw [h.x1, ptr_zero, coeffAddr, show 4 * (2 * i) = 8 * i by omega]
  have c1 : s.gpr .x1 + BitVec.ofNat 64 4 = coeffAddr (fP s₀) (2 * i + 1) := by
    rw [h.x1, ptr_add, coeffAddr, show 8 * i + 4 = 4 * (2 * i + 1) by omega]
  have d0 : s.gpr .x2 + BitVec.ofNat 64 0 = coeffAddr (gP s₀) (2 * i) := by
    rw [h.x2, ptr_zero, coeffAddr, show 4 * (2 * i) = 8 * i by omega]
  have d1 : s.gpr .x2 + BitVec.ofNat 64 4 = coeffAddr (gP s₀) (2 * i + 1) := by
    rw [h.x2, ptr_add, coeffAddr, show 8 * i + 4 = 4 * (2 * i + 1) by omega]
  have inF : ∀ j < 256, InRegions (s.rd ++ s.wr) (coeffAddr (fP s₀) j) 4 := fun j hj => by
    rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (List.mem_cons_self ..) (coeff_contains _ (show j < n from hj)))
  have inG : ∀ j < 256, InRegions (s.rd ++ s.wr) (coeffAddr (gP s₀) j) 4 := fun j hj => by
    rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd (in_regions (by simp) (coeff_contains _ (show j < n from hj)))
  have a0 := val_lt (F s₀)[2 * i]!
  have a1 := val_lt (F s₀)[2 * i + 1]!
  have b0 := val_lt (Gp s₀)[2 * i]!
  have b1 := val_lt (Gp s₀)[2 * i + 1]!
  have hγ := gammaTable_lt i hi
  have vF : ∀ j < 256, ∀ {t : State}, t.mem = s.mem → (t.mem.readW (coeffAddr (fP s₀) j) 32).toNat =
      ((F s₀)[j]!).val := fun j hj t ht => by
    rw [ht, ← coeffAt_eq, h.f j hj, polyAt_val hp.f (show j < n from hj)]
  have vG : ∀ j < 256, ∀ {t : State}, t.mem = s.mem → (t.mem.readW (coeffAddr (gP s₀) j) 32).toNat =
      ((Gp s₀)[j]!).val := fun j hj t ht => by
    rw [ht, ← coeffAt_eq, h.g j hj, polyAt_val hp.g (show j < n from hj)]
  refine wp_ldrw (a := coeffAddr (fP s₀) (2 * i)) (by decide) c0 (inF _ (by omega)) fun s₁ h₁ e₁ => ?_
  refine wp_ldrw (a := coeffAddr (fP s₀) (2 * i + 1)) (by decide) (by rw [h₁.get .x1]; exact c1)
    (by rw [h₁.rd, h₁.wr]; exact inF _ (by omega)) fun s₂ h₂ e₂ => ?_
  refine wp_ldrw (a := coeffAddr (gP s₀) (2 * i)) (by decide) (by rw [h₂.get .x2, h₁.get .x2]; exact d0)
    (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact inG _ (by omega)) fun s₃ h₃ e₃ => ?_
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have m₃ : s₃.mem = s.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  refine wp_ldrw (a := coeffAddr (gP s₀) (2 * i + 1)) (by decide) (by rw [k₃.get .x2]; exact d1)
    (by rw [k₃.rd, k₃.wr]; exact inG _ (by omega)) fun s₄ h₄ e₄ => ?_
  refine wp_ldrw (a := sP s₀ + BitVec.ofNat 64 (4 * i)) (by decide)
    (by rw [h₄.get .x3, k₃.get .x3, h.x3, ptr_zero]) ?_ fun s₅ h₅ e₅ => ?_
  · rw [h₄.rd, h₄.wr, k₃.rd, k₃.wr, h.rd, h.wr, hp.rd, hp.wr]
    exact in_rd_wr (in_regions (R := polyRegion (sP s₀)) (by simp) (contains_off (by omega) (by decide)))
  have k₅ := (k₃.trans h₄.keep).trans h₅.keep
  have m₅ : s₅.mem = s.mem := by rw [h₅.mem, h₄.mem, m₃]
  have v6 : (s₅.gpr .x6).toNat = ((F s₀)[2 * i]!).val := by
    rw [h₅.get .x6, h₄.get .x6, h₃.get .x6, h₂.get .x6, e₁, toNat_readW32, vF _ (by omega) rfl]
  have v7 : (s₅.gpr .x7).toNat = ((F s₀)[2 * i + 1]!).val := by
    rw [h₅.get .x7, h₄.get .x7, h₃.get .x7, e₂, toNat_readW32, vF _ (by omega) h₁.mem]
  have v12 : (s₅.gpr .x12).toNat = ((Gp s₀)[2 * i]!).val := by
    rw [h₅.get .x12, h₄.get .x12, e₃, toNat_readW32, vG _ (by omega) (by rw [h₂.mem, h₁.mem])]
  have v13 : (s₅.gpr .x13).toNat = ((Gp s₀)[2 * i + 1]!).val := by
    rw [h₅.get .x13, e₄, toNat_readW32, vG _ (by omega) m₃]
  have v14 : (s₅.gpr .x14).toNat = gammaTable.getD i 0 := by
    rw [e₅, toNat_readW32, h₄.mem, m₃, h.tab i hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have v9 : (s₅.gpr .x9).toNat = q := by rw [k₅.get .x9, h.x9]
  have v10 : (s₅.gpr .x10).toNat = 1290167 := by rw [k₅.get .x10, h.x10]
  -- f[2i+1] g[2i+1] mod q
  refine wp_mul fun s₆ h₆ e₆ => ?_
  have p₁ := mul_lt_q2 a1 b1
  have v₆ : (s₆.gpr .x15).toNat = ((F s₀)[2 * i + 1]!).val * ((Gp s₀)[2 * i + 1]!).val := by
    rw [e₆, toNat_mul_n (a := s₅.gpr .x7) (b := s₅.gpr .x13) (by rw [v7, v13]; omega), v7, v13]
  refine reduce_ok (by decide) (by decide) (by decide) (by omega) v₆ (by rw [h₆.get .x10, v10])
    (by rw [h₆.get .x9, v9]) fun s₇ h₇ e₇ => ?_
  -- times γ, plus f[2i] g[2i]
  refine wp_mul fun s₈ h₈ e₈ => wp_madd fun s₉ h₉ e₉ => ?_
  have k₇ := h₆.keep.trans h₇.keep
  have r₁ := Nat.mod_lt (((F s₀)[2 * i + 1]!).val * ((Gp s₀)[2 * i + 1]!).val) (show q > 0 by decide)
  have p₂ := mul_lt_q2 r₁ hγ
  have p₃ := mul_lt_q2 a0 b0
  have v₈ : (s₈.gpr .x15).toNat = ((F s₀)[2 * i + 1]!).val * ((Gp s₀)[2 * i + 1]!).val % q *
      gammaTable.getD i 0 := by
    have hb : (s₇.gpr .x15).toNat * (s₇.gpr .x14).toNat < 2 ^ 64 := by
      rw [e₇, k₇.get .x14, v14]; omega
    rw [e₈, toNat_mul_n hb, e₇, k₇.get .x14, v14]
  have v₉ : (s₉.gpr .x15).toNat = ((F s₀)[2 * i + 1]!).val * ((Gp s₀)[2 * i + 1]!).val % q *
      gammaTable.getD i 0 + ((F s₀)[2 * i]!).val * ((Gp s₀)[2 * i]!).val := by
    have hb : (s₈.gpr .x15).toNat + (s₈.gpr .x6).toNat * (s₈.gpr .x12).toNat < 2 ^ 64 := by
      rw [v₈, h₈.get .x6, h₈.get .x12, k₇.get .x6, k₇.get .x12, v6, v12]; omega
    rw [e₉, toNat_madd_n hb, v₈, h₈.get .x6, h₈.get .x12, k₇.get .x6, k₇.get .x12, v6, v12]
  have k₉ := (k₇.trans h₈.keep).trans h₉.keep
  refine reduce_ok (by decide) (by decide) (by decide) (by omega) v₉ (by rw [k₉.get .x10, v10])
    (by rw [k₉.get .x9, v9]) fun s₁₀ h₁₀ e₁₀ => ?_
  have k₁₀ := k₉.trans h₁₀.keep
  refine wp_strw (a := coeffAddr (hP s₀) (2 * i)) (by decide) ?_ ?_ fun s₁₁ h₁₁ => ?_
  · rw [k₁₀.get .x0, k₅.get .x0, h.x0, ptr_zero, coeffAddr, show 4 * (2 * i) = 8 * i by omega]
  · rw [k₁₀.wr, k₅.wr, h.wr, hp.wr]
    exact in_regions (List.mem_cons_self ..) (coeff_contains _ (show 2 * i < n by rw [n_eq]; omega))
  -- f[2i] g[2i+1] + f[2i+1] g[2i]
  refine wp_mul fun s₁₂ h₁₂ e₁₂ => wp_madd fun s₁₃ h₁₃ e₁₃ => ?_
  have k₁₁ := k₁₀.trans h₁₁.keep
  have p₄ := mul_lt_q2 a0 b1
  have p₅ := mul_lt_q2 a1 b0
  have v₁₂ : (s₁₂.gpr .x15).toNat = ((F s₀)[2 * i]!).val * ((Gp s₀)[2 * i + 1]!).val := by
    have hb : (s₁₁.gpr .x6).toNat * (s₁₁.gpr .x13).toNat < 2 ^ 64 := by
      rw [k₁₁.get .x6, k₁₁.get .x13, v6, v13]; omega
    rw [e₁₂, toNat_mul_n hb, k₁₁.get .x6, k₁₁.get .x13, v6, v13]
  have v₁₃ : (s₁₃.gpr .x15).toNat = ((F s₀)[2 * i]!).val * ((Gp s₀)[2 * i + 1]!).val +
      ((F s₀)[2 * i + 1]!).val * ((Gp s₀)[2 * i]!).val := by
    have hb : (s₁₂.gpr .x15).toNat + (s₁₂.gpr .x7).toNat * (s₁₂.gpr .x12).toNat < 2 ^ 64 := by
      rw [v₁₂, h₁₂.get .x7, h₁₂.get .x12, k₁₁.get .x7, k₁₁.get .x12, v7, v12]; omega
    rw [e₁₃, toNat_madd_n hb, v₁₂, h₁₂.get .x7, h₁₂.get .x12, k₁₁.get .x7, k₁₁.get .x12, v7, v12]
  have k₁₃ := (k₁₁.trans h₁₂.keep).trans h₁₃.keep
  refine reduce_ok (by decide) (by decide) (by decide) (by omega) v₁₃ (by rw [k₁₃.get .x10, v10])
    (by rw [k₁₃.get .x9, v9]) fun s₁₄ h₁₄ e₁₄ => ?_
  have k₁₄ := k₁₃.trans h₁₄.keep
  refine wp_strw (a := coeffAddr (hP s₀) (2 * i + 1)) (by decide) ?_ ?_ fun s₁₅ h₁₅ => ?_
  · rw [k₁₄.get .x0, k₅.get .x0, h.x0, ptr_add, coeffAddr, show 8 * i + 4 = 4 * (2 * i + 1) by omega]
  · rw [k₁₄.wr, k₅.wr, h.wr, hp.wr]
    exact in_regions (List.mem_cons_self ..) (coeff_contains _ (show 2 * i + 1 < n by rw [n_eq]; omega))
  refine wp_addImm (by decide) fun s₁₆ h₁₆ e₁₆ => wp_addImm (by decide) fun s₁₇ h₁₇ e₁₇ =>
    wp_addImm (by decide) fun s₁₈ h₁₈ e₁₈ => wp_addImm (by decide) fun s₁₉ h₁₉ e₁₉ =>
    wp_subImm (by decide) fun s₂₀ h₂₀ e₂₀ => wp_nil ?_
  have k₁₅ := k₁₄.trans h₁₅.keep
  have k₁₉ := (((k₁₅.trans h₁₆.keep).trans h₁₇.keep).trans h₁₈.keep).trans h₁₉.keep
  have k₂₀ := k₁₉.trans h₂₀.keep
  have c11 : (s₁₉.gpr .x11).toNat = 128 - i := by rw [k₁₉.get .x11, k₅.get .x11, h.x11]
  have v11 : (s₂₀.gpr .x11).toNat = 128 - (i + 1) := by
    rw [e₂₀, toNat_sub_n (by rw [c11]; simp; omega), c11]
    simp
    omega
  have m₂₀ : s₂₀.mem = (s.mem.writeW (coeffAddr (hP s₀) (2 * i)) ((s₁₀.gpr .x15).setWidth 32)).writeW
      (coeffAddr (hP s₀) (2 * i + 1)) ((s₁₄.gpr .x15).setWidth 32) := by
    rw [h₂₀.mem, h₁₉.mem, h₁₈.mem, h₁₇.mem, h₁₆.mem, h₁₅.mem, h₁₄.mem, h₁₃.mem, h₁₂.mem, h₁₁.mem,
      h₁₀.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, m₅]
  have fr : Frame [polyRegion (hP s₀)] s.mem s₂₀.mem := by
    rw [m₂₀]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (coeff_contains _ (show 2 * i < n by rw [n_eq]; omega))).writeW (List.mem_singleton_self _) _
      (coeff_contains _ (show 2 * i + 1 < n by rw [n_eq]; omega))
  have dj : ∀ {R : Region}, R.Disjoint (polyRegion (hP s₀)) → ∀ r ∈ [polyRegion (hP s₀)], R.Disjoint r :=
    fun hd r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd
  refine ⟨⟨by rw [k₂₀.rd, k₅.rd, h.rd], by rw [k₂₀.wr, k₅.wr, h.wr], by rw [k₂₀.sp, k₅.sp, h.sp],
    ?_, ?_, ?_, ?_, by rw [k₂₀.get .x9, v9], by rw [k₂₀.get .x10, v10], v11, ?_, fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_⟩, by rw [v11]; omega⟩
  · rw [h₂₀.get .x0, h₁₉.get .x0, h₁₈.get .x0, h₁₇.get .x0, e₁₆, k₁₅.get .x0, k₅.get .x0, h.x0,
      ptr_next]
  · rw [h₂₀.get .x1, h₁₉.get .x1, h₁₈.get .x1, e₁₇, h₁₆.get .x1, k₁₅.get .x1, k₅.get .x1, h.x1,
      ptr_next]
  · rw [h₂₀.get .x2, h₁₉.get .x2, e₁₈, h₁₇.get .x2, h₁₆.get .x2, k₁₅.get .x2, k₅.get .x2, h.x2,
      ptr_next]
  · rw [h₂₀.get .x3, e₁₉, h₁₈.get .x3, h₁₇.get .x3, h₁₆.get .x3, k₁₅.get .x3, k₅.get .x3, h.x3,
      ptr_next]
  · rw [m₂₀, show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
    refine (h.out.write (by omega) ?_).write (by omega) ?_
    · rw [setWidth32_of_toNat e₁₀, G_even _ hi]
    · rw [setWidth32_of_toNat e₁₄, G_odd _ hi]
  · rw [coeffAt_frame fr (dj hp.hf.symm) hj, h.f j hj]
  · rw [coeffAt_frame fr (dj hp.hg.symm) hj, h.g j hj]
  · rw [fr.readW (r := ⟨sP s₀, 1024⟩) (contains_off (by omega) (by decide)) (dj hp.hs.symm) (by decide),
      h.tab j hj]

theorem correct (s₀ : State) (hs : mulAArch64.pre s₀) :
    ∃ t s', Exec isa multiplyNTTs s₀ t s' ∧ abiPreserved s₀ s' ∧ mulAArch64.post s₀ s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hs
  have hp : Pre s₀ := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  suffices h : WP isa multiplyNTTs s₀ fun s' => s'.sp = s₀.sp ∧ mulAArch64.post s₀ s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (table_ok gammaTable (fun k hk => Nat.lt_trans (gammaTable_lt k hk) (by decide))
    (b := .x3) (by decide) fun k hk => by
      rw [hp.wr]
      exact in_regions (R := polyRegion (sP s₀)) (by simp) (contains_off (by omega) (by decide)))
    fun s₁ h₁ => ?_
  refine WP.mono (consts_ok s₁) fun s₃ ⟨h₃, e₂, e₃⟩ => ?_
  refine wp_movz fun s₄ h₄ e₄ => wp_nil ?_
  have k₄ := (h₁.keep.trans h₃.keep).trans h₄.keep
  have m₄ : s₄.mem = s₁.mem := by rw [h₄.mem, h₃.mem]
  have dj : ∀ {R : Region}, R.Disjoint (polyRegion (sP s₀)) →
      ∀ r ∈ [(⟨s₀.gpr .x3, 512⟩ : Region)], R.Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hd.sub_right (Region.sub_prefix (by decide))
  have i₀ : Inv s₀ 0 s₄ := by
    refine ⟨k₄.rd, k₄.wr, k₄.sp, by rw [k₄.get .x0, Nat.mul_zero, ptr_zero],
      by rw [k₄.get .x1, Nat.mul_zero, ptr_zero], by rw [k₄.get .x2, Nat.mul_zero, ptr_zero],
      by rw [k₄.get .x3, Nat.mul_zero, ptr_zero], by rw [h₄.get .x9, e₂],
      by rw [h₄.get .x10, e₃], by rw [e₄]; rfl, ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rw [m₄, Nat.mul_zero]
      intro j hj
      rw [ite_eq_right (Nat.not_lt_zero j), old, coeffAt_frame h₁.frame (dj hp.hs) hj]
    · rw [m₄, coeffAt_frame h₁.frame (dj hp.fs) hj]
    · rw [m₄, coeffAt_frame h₁.frame (dj hp.gs) hj]
    · rw [m₄]; exact h₁.tab j hj
  refine WP.mono (count_loop (by decide) (Inv s₀) (fun i hi s h => step hp hi h) i₀)
    fun s' h => ⟨h.sp, (show CoeffsUpTo _ _ 256 _ _ from h.out).polyIs fun _ _ => rfl⟩

theorem ct : ConstantTime isa mulAArch64.pre mulAArch64.pub multiplyNTTs :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => agree_of hsp (by simp [h0, h1, h2, h3])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]
  wr := [⟨0x1000, 1024⟩, ⟨0x4000, 1024⟩]

theorem mul_verified :
    Verified AArch64.target multiplyNTTs (Spec.MlKem.mulContract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Spec.MlKem.mulContract, Spec.MlKem.mulSig, mulAArch64, AArch64.abi,
      AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.Mul
