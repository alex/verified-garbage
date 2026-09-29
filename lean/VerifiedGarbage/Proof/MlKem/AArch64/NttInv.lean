import VerifiedGarbage.Proof.MlKem.AArch64.NttFwd

/-!
# ML-KEM on AArch64: `vg_mlkem_ntt_inv`

Untrusted: everything here is checked by Lean. As the NTT
(`NttFwd.lean`), with the inverse butterflies, `len` doubling and the zetas
read backwards (`nttInv_eq_layers`); then every coefficient times 3303
(`scale_step`).
-/

namespace VG.Proof.MlKem.AArch64.Ntt

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem

/-- The layers of `NTT⁻¹`: `len = 2^(i+1)`, `64 / 2ⁱ` blocks. -/
theorem ifacts : ∀ i < 7, 0 < 2 ^ (i + 1) ∧ 128 / 2 ^ (i + 1) = 64 / 2 ^ i ∧
    2 ^ (i + 1) * (64 / 2 ^ i) = 128 ∧ 256 / 2 ^ (i + 1) = 2 * (64 / 2 ^ i) ∧
    256 / 2 ^ (i + 1) - 1 - 64 / 2 ^ i = 256 / 2 ^ (i + 2) - 1 ∧ 2 ^ (i + 1) * 2 ^ 1 = 2 ^ (i + 2) ∧
    64 / 2 ^ i / 2 ^ 1 = 64 / 2 ^ (i + 1) ∧ nttInvLens.getD i 0 = 2 ^ (i + 1) ∧
    2 * (64 / 2 ^ i) ≤ 128 ∧ 0 < 64 / 2 ^ i ∧ 2 ^ (i + 1) ≤ 128 := by
  decide

/-- After `b` blocks of the layer with `len`. -/
structure LInvI (s₀ : State) (P : Poly) (len : Nat) (L : State) (b : Nat) (u : State) : Prop where
  st : St s₀ u
  keep : Keep kRegs L u
  x2 : u.gpr .x2 = fP s₀ + BitVec.ofNat 64 (4 * (2 * len * b))
  x12 : u.gpr .x12 = sP s₀ + BitVec.ofNat 64 (4 * (256 / len - 1 - b))
  x16 : (u.gpr .x16).toNat = 128 / len - b
  poly : PolyIs u.mem (fP s₀) (nttInvLayerN P len b)

theorem ptr_prev (p : Addr) {k : Nat} (hk : 1 ≤ k) :
    p + BitVec.ofNat 64 (4 * k) - BitVec.ofNat 64 4 = p + BitVec.ofNat 64 (4 * (k - 1)) := by
  rw [show 4 * k = 4 * (k - 1) + 4 by omega, ← ptr_add, BitVec.add_sub_cancel]

/-- One block. -/
theorem iblock_step {s₀ : State} (hp : Pre s₀) {P : Poly} {len : Nat} (hlen : 0 < len)
    (hnb : len * (128 / len) = 128) (h256 : 256 / len = 2 * (128 / len)) (hk : 2 * (128 / len) ≤ 128)
    {L : State} (h11 : (L.gpr .x11).toNat = len) (h15 : (L.gpr .x15).toNat = len * 4) {b : Nat}
    (hb : b < 128 / len) {u : State} (h : LInvI s₀ P len L b u) :
    WP isa nttInvBlockCode u fun u' => LInvI s₀ P len L (b + 1) u' ∧
      ((u'.gpr .x16).toNat ≠ 0 ↔ b + 1 ≠ 128 / len) := by
  have hbl : 2 * len * b + 2 * len ≤ 256 := by
    have : len * (b + 1) ≤ len * (128 / len) := Nat.mul_le_mul_left _ hb
    rw [Nat.mul_succ] at this
    rw [Nat.mul_assoc]
    omega
  have hk' : 256 / len - 1 - b < 128 := by omega
  refine WP.seq (wp_ldrw (a := sP s₀ + BitVec.ofNat 64 (4 * (256 / len - 1 - b))) (by decide)
    (by rw [h.x12, ptr_zero]) (hp.in_tab h.st hk') fun u₁ h₁ e₁ => ?_)
  refine wp_subImm (by decide) fun u₂ h₂ e₂ => wp_add fun u₃ h₃ e₃ => wp_addImm (by decide)
    fun u₄ h₄ e₄ => wp_nil ?_
  have k₄ := ((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep
  have m₄ : u₄.mem = u.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have st₄ : St s₀ u₄ := h.st.keep k₄ m₄
  refine WP.seq (WP.mono (inner_ok ibfly_spec hp (P := nttInvLayerN P len b)
    (Z := zeta (256 / len - 1 - b)) (start := 2 * len * b) hlen hbl st₄ ?_ ?_ ?_ ?_ ?_)
    fun u₅ ⟨st₅, k₅, x2₅, x3₅, p₅⟩ => ?_)
  · rw [k₄.get .x2, h.x2]
  · have e15 : u₂.gpr .x15 = BitVec.ofNat 64 (len * 4) := by
      apply BitVec.eq_of_toNat_eq
      rw [h₂.get .x15, h₁.get .x15, h.keep.get .x15, h15, toNat_ofNat_lt (by omega)]
    rw [h₄.get .x3, e₃, h₂.get .x2, h₁.get .x2, h.x2, e15, ptr_add]
    congr 2; rw [Nat.mul_comm len 4, Nat.mul_add]
  · have : u₄.gpr .x5 = L.gpr .x11 := by
      rw [e₄, ptr_zero, h₃.get .x11, h₂.get .x11, h₁.get .x11, h.keep.get .x11]
    rw [this, h11]
  · rw [h₄.get .x17, h₃.get .x17, h₂.get .x17, e₁, zeta_load h.st hk']
  · rw [m₄]; exact h.poly
  refine wp_addImm (by decide) fun u₆ h₆ e₆ => wp_subImm (by decide) fun u₇ h₇ e₇ => wp_nil ?_
  have k₇ := (k₅.trans h₆.keep).trans h₇.keep
  have c16 : (u₆.gpr .x16).toNat = 128 / len - b := by
    rw [h₆.get .x16, k₅.get .x16, k₄.get .x16, h.x16]
  have v16 : (u₇.gpr .x16).toNat = 128 / len - (b + 1) := by
    rw [e₇, toNat_sub_n (by rw [c16]; simp; omega), c16]
    simp
    omega
  refine ⟨⟨st₅.keep (h₆.keep.trans h₇.keep) (by rw [h₇.mem, h₆.mem]),
    (((h.keep.trans k₄).trans k₅).trans (h₆.keep.trans h₇.keep)).mono, ?_, ?_, v16, ?_⟩,
    by rw [v16]; omega⟩
  · rw [h₇.get .x2, e₆, ptr_zero, x3₅, show 2 * len * b + 2 * len = 2 * len * (b + 1) by
      rw [Nat.mul_succ]]
  · rw [h₇.get .x12, h₆.get .x12, k₅.get .x12, h₄.get .x12, h₃.get .x12, e₂, h₁.get .x12, h.x12,
      ptr_prev _ (by omega), Nat.sub_sub _ b 1]
  · rw [h₇.mem, h₆.mem, nttInvLayerN_succ]
    exact p₅

/-- After `i` layers. -/
structure OInvI (s₀ : State) (i : Nat) (u : State) : Prop where
  st : St s₀ u
  x11 : (u.gpr .x11).toNat = 2 ^ (i + 1)
  x12 : u.gpr .x12 = sP s₀ + BitVec.ofNat 64 (4 * (256 / 2 ^ (i + 1) - 1))
  x13 : (u.gpr .x13).toNat = 64 / 2 ^ i
  x14 : (u.gpr .x14).toNat = 7 - i
  poly : PolyIs u.mem (fP s₀) ((nttInvLens.take i).foldl nttInvLayer (P₀ s₀))

/-- One layer. -/
theorem ilayer_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 7) {u : State} (h : OInvI s₀ i u) :
    WP isa nttInvLayerCode u fun u' => OInvI s₀ (i + 1) u' ∧ ((u'.gpr .x14).toNat ≠ 0 ↔ i + 1 ≠ 7) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := ifacts i hi
  refine WP.seq (wp_mov fun u₁ h₁ e₁ => wp_mov fun u₂ h₂ e₂ => wp_lsl (by decide) fun u₃ h₃ e₃ =>
    wp_nil ?_)
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have m₃ : u₃.mem = u.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  have c11 : (u₃.gpr .x11).toNat = 2 ^ (i + 1) := by rw [k₃.get .x11, h.x11]
  have c15 : (u₃.gpr .x15).toNat = 2 ^ (i + 1) * 4 := by
    rw [e₃, toNat_lsl_n (by rw [h₂.get .x11, h₁.get .x11, h.x11]; omega), h₂.get .x11, h₁.get .x11,
      h.x11]
  have l₀ : LInvI s₀ ((nttInvLens.take i).foldl nttInvLayer (P₀ s₀)) (2 ^ (i + 1)) u₃ 0 u₃ := by
    refine ⟨h.st.keep k₃ m₃, Keep.refl _ _, ?_, ?_, ?_, by rw [m₃, nttInvLayerN_zero]; exact h.poly⟩
    · rw [h₃.get .x2, h₂.get .x2, e₁, h.st.x0, Nat.mul_zero, Nat.mul_zero, ptr_zero]
    · rw [k₃.get .x12, h.x12, Nat.sub_zero]
    · rw [h₃.get .x16, e₂, h₁.get .x13, h.x13, f1, Nat.sub_zero]
  refine WP.seq (WP.mono (count_loop (n := 128 / 2 ^ (i + 1)) (by rw [f1]; exact f9)
    (LInvI s₀ _ (2 ^ (i + 1)) u₃) (fun b hb v hv => iblock_step hp f0 (by rw [f1]; omega)
      (by rw [f3, f1]) (by rw [f1]; omega) c11 c15 hb hv) l₀) fun u₄ h₄ => ?_)
  refine wp_lsl (by decide) fun u₅ h₅ e₅ => wp_lsr (by decide) fun u₆ h₆ e₆ => wp_subImm (by decide)
    fun u₇ h₇ e₇ => wp_nil ?_
  have k₇ := (h₅.keep.trans h₆.keep).trans h₇.keep
  have c14 : (u₆.gpr .x14).toNat = 7 - i := by
    rw [h₆.get .x14, h₅.get .x14, h₄.keep.get .x14, k₃.get .x14, h.x14]
  have v14 : (u₇.gpr .x14).toNat = 7 - (i + 1) := by
    rw [e₇, toNat_sub_n (by rw [c14]; simp; omega), c14]
    simp
    omega
  have c13 : (u₅.gpr .x13).toNat = 64 / 2 ^ i := by
    rw [h₅.get .x13, h₄.keep.get .x13, k₃.get .x13, h.x13]
  refine ⟨⟨h₄.st.keep k₇ (by rw [h₇.mem, h₆.mem, h₅.mem]), ?_, ?_, ?_, v14, ?_⟩, by rw [v14]; omega⟩
  · rw [h₇.get .x11, h₆.get .x11, e₅, toNat_lsl_n (by rw [h₄.keep.get .x11, c11]; omega),
      h₄.keep.get .x11, c11, f5]
  · rw [k₇.get .x12, h₄.x12, f1, f4]
  · rw [h₇.get .x13, e₆, toNat_lsr, c13, f6]
  · rw [h₇.mem, h₆.mem, h₅.mem, foldl_take_succ _ _ _ 0 (by rw [show nttInvLens.length = 7 from rfl]; exact hi),
      f7]
    exact h₄.poly

/-! ## The scaling by 3303 -/

section
variable (R : Poly)

/-- Coefficient `i` after the scaling. -/
def SG (i : Nat) : BitVec 32 := BitVec.ofNat 32 (R[i]! * 3303).val
/-- Coefficient `i` before it. -/
def SO (i : Nat) : BitVec 32 := BitVec.ofNat 32 (R[i]!).val

end

/-- After `k` coefficients scaled. -/
structure SInv (s₀ : State) (R : Poly) (k : Nat) (u : State) : Prop where
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  sp : u.sp = s₀.sp
  x2 : u.gpr .x2 = fP s₀ + BitVec.ofNat 64 (4 * k)
  x5 : (u.gpr .x5).toNat = 256 - k
  x9 : (u.gpr .x9).toNat = q
  x10 : (u.gpr .x10).toNat = 1290167
  x17 : (u.gpr .x17).toNat = 3303
  out : CoeffsUpTo u.mem (fP s₀) k (SG R) (SO R)

theorem scale_val (a : Zq) : (a * 3303).val = a.val * 3303 % q := by
  rw [val_mul]; rfl

theorem scale_step {s₀ : State} (hp : Pre s₀) {R : Poly} {k : Nat} (hk : k < 256) {u : State}
    (h : SInv s₀ R k u) :
    WP isa (.block scaleBody) u fun u' =>
      SInv s₀ R (k + 1) u' ∧ ((u'.gpr .x5).toNat ≠ 0 ↔ k + 1 ≠ 256) := by
  have hq : q = 3329 := rfl
  have hk' : k < n := hk
  rw [show scaleBody = .ldr .w .x6 .x2 0 :: .mul .x .x6 .x6 .x17 :: (barrett .x6 .x8 .x10 .x9 ++
    (csub .x6 .x8 .x9 ++ ([.str .w .x6 .x2 0, .addImm .x .x2 .x2 4, .subImm .x .x5 .x5 1] :
      List Instr))) from rfl]
  have a := val_lt R[k]!
  have c : (u.mem.readW (coeffAddr (fP s₀) k) 32).toNat = (R[k]!).val := by
    rw [← coeffAt_eq, h.out k hk, ite_eq_right (Nat.lt_irrefl k), SO, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  refine wp_ldrw (a := coeffAddr (fP s₀) k) (by decide) (by rw [h.x2, ptr_zero]) ?_
    fun u₁ h₁ e₁ => wp_mul fun u₂ h₂ e₂ => ?_
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    exact in_regions (List.mem_cons_self ..) (coeff_contains _ hk')
  have v₂ : (u₂.gpr .x6).toNat = (R[k]!).val * 3303 := by
    have hb : (u₁.gpr .x6).toNat * (u₁.gpr .x17).toNat < 2 ^ 64 := by
      rw [e₁, toNat_readW32, c, h₁.get .x17, h.x17]; omega
    rw [e₂, toNat_mul_n hb, e₁, toNat_readW32, c, h₁.get .x17, h.x17]
  have k₂ := h₁.keep.trans h₂.keep
  refine reduce_ok (by decide) (by decide) (by decide) (by omega) v₂ (by rw [k₂.get .x10, h.x10])
    (by rw [k₂.get .x9, h.x9]) fun u₃ h₃ e₃ => ?_
  have k₃ := k₂.trans h₃.keep
  refine wp_strw (a := coeffAddr (fP s₀) k) (by decide) (by rw [k₃.get .x2, h.x2, ptr_zero]) ?_
    fun u₄ h₄ => wp_addImm (by decide) fun u₅ h₅ e₅ => wp_subImm (by decide) fun u₆ h₆ e₆ =>
      wp_nil ?_
  · rw [k₃.wr, h.wr, hp.wr]
    exact in_regions (List.mem_cons_self ..) (coeff_contains _ hk')
  have k₆ := ((k₃.trans h₄.keep).trans h₅.keep).trans h₆.keep
  have c5 : (u₅.gpr .x5).toNat = 256 - k := by
    rw [h₅.get .x5, h₄.gpr, k₃.get .x5, h.x5]
  have v5 : (u₆.gpr .x5).toNat = 256 - (k + 1) := by
    rw [e₆, toNat_sub_n (by rw [c5]; simp; omega), c5]
    simp
    omega
  have m₆ : u₆.mem = u.mem.writeW (coeffAddr (fP s₀) k) ((u₃.gpr .x6).setWidth 32) := by
    rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨⟨by rw [k₆.rd, h.rd], by rw [k₆.wr, h.wr], by rw [k₆.sp, h.sp], ?_, v5,
    by rw [k₆.get .x9, h.x9], by rw [k₆.get .x10, h.x10], by rw [k₆.get .x17, h.x17], ?_⟩,
    by rw [v5]; omega⟩
  · rw [h₆.get .x2, e₅, h₄.gpr, k₃.get .x2, h.x2, ptr_next]
  · rw [m₆]
    exact h.out.write hk (by rw [setWidth32_of_toNat e₃, SG, scale_val])

/-! ## `NTT⁻¹` -/

theorem correctInv (s₀ : State) (hs : (inPlaceAArch64 nttInv).pre s₀) :
    ∃ t s', Exec isa Impl.MlKem.AArch64.nttInv s₀ t s' ∧ abiPreserved s₀ s' ∧
      (inPlaceAArch64 nttInv).post s₀ s' := by
  have hp := pre_of hs
  suffices h : WP isa Impl.MlKem.AArch64.nttInv s₀ fun s' => s'.sp = s₀.sp ∧
      (inPlaceAArch64 nttInv).post s₀ s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hpost⟩
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (table_ok zetaTable (fun k hk => Nat.lt_trans (zetaTable_lt k hk) (by decide))
    (b := .x1) (by decide) fun k hk => by
      rw [hp.wr]
      exact in_regions (R := polyRegion (sP s₀)) (by simp) (contains_off (by omega) (by decide)))
    fun s₁ h₁ => ?_
  refine WP.mono (consts_ok s₁) fun s₂ ⟨h₂, e₉, e₁₀⟩ => ?_
  refine wp_movz fun s₃ h₃ e₃ => wp_addImm (by decide) fun s₄ h₄ e₄ => wp_movz fun s₅ h₅ e₅ =>
    wp_movz fun s₆ h₆ e₆ => wp_nil ?_
  have k₆ := ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆.keep
  have m₆ : s₆.mem = s₁.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem]
  have fr : ∀ r ∈ [(⟨s₀.gpr .x1, 512⟩ : Region)], (polyRegion (fP s₀)).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.disj.sub_right (Region.sub_prefix (by decide))
  have i₀ : OInvI s₀ 0 s₆ := by
    refine ⟨⟨k₆.rd, k₆.wr, k₆.sp, k₆.get .x0, ?_, ?_, fun k hk => by rw [m₆]; exact h₁.tab k hk⟩,
      by rw [h₆.get .x11, h₅.get .x11, h₄.get .x11, e₃]; rfl, ?_,
      by rw [h₆.get .x13, e₅]; rfl, by rw [e₆]; rfl, ?_⟩
    · rw [h₆.get .x9, h₅.get .x9, h₄.get .x9, h₃.get .x9, e₉]
    · rw [h₆.get .x10, h₅.get .x10, h₄.get .x10, h₃.get .x10, e₁₀]
    · rw [h₆.get .x12, h₅.get .x12, e₄, h₃.get .x1, h₂.get .x1, h₁.keep.get .x1]
    · rw [m₆]
      exact polyIs_frame h₁.frame fr ⟨hp.red, rfl⟩
  refine WP.seq (WP.mono (count_loop (by decide) (OInvI s₀) (fun i hi u h => ilayer_step hp hi h) i₀)
    fun u h => ?_)
  refine WP.seq (wp_movz fun u₁ h₁ e₁ => wp_mov fun u₂ h₂ e₂ => wp_movz fun u₃ h₃ e₃ => wp_nil ?_)
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have m₃ : u₃.mem = u.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  have hR : PolyIs u₃.mem (fP s₀) (nttInvLens.foldl nttInvLayer (P₀ s₀)) := by
    rw [m₃]; exact h.poly
  have s₀' : SInv s₀ (nttInvLens.foldl nttInvLayer (P₀ s₀)) 0 u₃ := by
    refine ⟨by rw [k₃.rd, h.st.rd], by rw [k₃.wr, h.st.wr], by rw [k₃.sp, h.st.sp], ?_,
      by rw [e₃]; rfl, by rw [k₃.get .x9, h.st.x9], by rw [k₃.get .x10, h.st.x10],
      by rw [h₃.get .x17, h₂.get .x17, e₁]; rfl, fun i hi => ?_⟩
    · rw [h₃.get .x2, e₂, h₁.get .x0, h.st.x0, Nat.mul_zero, ptr_zero]
    · rw [ite_eq_right (Nat.not_lt_zero i), polyIs_coeffAt hR (show i < n from hi), SO]
  refine WP.mono (count_loop (by decide) (SInv s₀ _) (fun k hk v hv => scale_step hp hk hv) s₀')
    fun s' hs' => ⟨hs'.sp, ?_⟩
  show PolyIs s'.mem (fP s₀) (nttInv (P₀ s₀))
  refine hs'.out.polyIs fun i hi => ?_
  rw [SG, nttInv_eq_layers, map_mul_get _ (show i < n from hi)]

theorem ctInv : ConstantTime isa (inPlaceAArch64 nttInv).pre (inPlaceAArch64 nttInv).pub
    Impl.MlKem.AArch64.nttInv :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ ⟨h0, h1, hsp⟩ => agree_of hsp (by simp [h0, h1])) (by taint_decide)

theorem ntt_inv_verified :
    Verified AArch64.target Impl.MlKem.AArch64.nttInv (Spec.MlKem.nttInvContract AArch64.abi) :=
  Verified.of_correct correctInv ctInv (by
    mlkem_implies [Spec.MlKem.nttInvContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig,
      inPlaceAArch64, AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.Ntt
