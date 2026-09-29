import VerifiedGarbage.Proof.MlKem.AArch64.NttLoop

/-!
# ML-KEM on AArch64: `vg_mlkem_ntt`

Untrusted: everything here is checked by Lean. The blocks of a layer
(`layer_ok`, `nttLayerN`), and the seven layers (`ntt_eq_layers`).
-/

namespace VG.Proof.MlKem.AArch64.Ntt

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem

theorem foldl_take_succ {α β : Type} (g : α → β → α) (x : α) (L : List β) (d : β) {i : Nat}
    (hi : i < L.length) : (L.take (i + 1)).foldl g x = g ((L.take i).foldl g x) (L.getD i d) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.foldl_append, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi]
  rfl

/-- The layers of the NTT: `len = 128 / 2ⁱ`, `2ⁱ` blocks. -/
theorem lfacts : ∀ i < 7, 0 < 128 / 2 ^ i ∧ 128 / (128 / 2 ^ i) = 2 ^ i ∧ 128 / 2 ^ i * 2 ^ i = 128 ∧
    2 ^ i ≤ 64 ∧ 128 / 2 ^ i / 2 = 128 / 2 ^ (i + 1) ∧ nttLens.getD i 0 = 128 / 2 ^ i ∧
    128 / 2 ^ i ≤ 128 := by
  decide

/-- The registers a block changes. -/
abbrev kRegs : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x12, .x16, .x17]

/-- After `b` blocks of the layer with `len`. -/
structure LInv (s₀ : State) (P : Poly) (len : Nat) (L : State) (b : Nat) (u : State) : Prop where
  st : St s₀ u
  keep : Keep kRegs L u
  x2 : u.gpr .x2 = fP s₀ + BitVec.ofNat 64 (4 * (2 * len * b))
  x12 : u.gpr .x12 = sP s₀ + BitVec.ofNat 64 (4 * (128 / len + b))
  x16 : (u.gpr .x16).toNat = 128 / len - b
  poly : PolyIs u.mem (fP s₀) (nttLayerN P len b)

/-- One block. -/
theorem block_step {s₀ : State} (hp : Pre s₀) {P : Poly} {len : Nat} (hlen : 0 < len)
    (hnb : len * (128 / len) = 128) (hk : 2 * (128 / len) ≤ 128) {L : State}
    (h11 : (L.gpr .x11).toNat = len) (h15 : (L.gpr .x15).toNat = len * 4) {b : Nat}
    (hb : b < 128 / len) {u : State} (h : LInv s₀ P len L b u) :
    WP isa nttBlockCode u fun u' => LInv s₀ P len L (b + 1) u' ∧
      ((u'.gpr .x16).toNat ≠ 0 ↔ b + 1 ≠ 128 / len) := by
  have hbl : 2 * len * b + 2 * len ≤ 256 := by
    have : len * (b + 1) ≤ len * (128 / len) := Nat.mul_le_mul_left _ hb
    rw [Nat.mul_succ] at this
    rw [Nat.mul_assoc]
    omega
  have hk' : 128 / len + b < 128 := by omega
  refine WP.seq (wp_ldrw (a := sP s₀ + BitVec.ofNat 64 (4 * (128 / len + b))) (by decide)
    (by rw [h.x12, ptr_zero]) (hp.in_tab h.st hk') fun u₁ h₁ e₁ => ?_)
  refine wp_addImm (by decide) fun u₂ h₂ e₂ => wp_add fun u₃ h₃ e₃ => wp_addImm (by decide)
    fun u₄ h₄ e₄ => wp_nil ?_
  have k₄ := ((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep
  have m₄ : u₄.mem = u.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have st₄ : St s₀ u₄ := h.st.keep k₄ m₄
  refine WP.seq (WP.mono (inner_ok bfly_spec hp (P := nttLayerN P len b) (Z := zeta (128 / len + b)) (start := 2 * len * b)
    hlen hbl st₄ ?_ ?_ ?_ ?_ ?_) fun u₅ ⟨st₅, k₅, x2₅, x3₅, p₅⟩ => ?_)
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
      ptr_next]
    rfl
  · rw [h₇.mem, h₆.mem, nttLayerN_succ]
    exact p₅

/-- After `i` layers. -/
structure OInv (s₀ : State) (i : Nat) (u : State) : Prop where
  st : St s₀ u
  x11 : (u.gpr .x11).toNat = 128 / 2 ^ i
  x12 : u.gpr .x12 = sP s₀ + BitVec.ofNat 64 (4 * 2 ^ i)
  x13 : (u.gpr .x13).toNat = 2 ^ i
  x14 : (u.gpr .x14).toNat = 7 - i
  poly : PolyIs u.mem (fP s₀) ((nttLens.take i).foldl nttLayer (P₀ s₀))

/-- One layer. -/
theorem layer_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 7) {u : State} (h : OInv s₀ i u) :
    WP isa nttLayerCode u fun u' => OInv s₀ (i + 1) u' ∧ ((u'.gpr .x14).toNat ≠ 0 ↔ i + 1 ≠ 7) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6⟩ := lfacts i hi
  refine WP.seq (wp_mov fun u₁ h₁ e₁ => wp_mov fun u₂ h₂ e₂ => wp_lsl (by decide) fun u₃ h₃ e₃ =>
    wp_nil ?_)
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have m₃ : u₃.mem = u.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  have c11 : (u₃.gpr .x11).toNat = 128 / 2 ^ i := by rw [k₃.get .x11, h.x11]
  have c15 : (u₃.gpr .x15).toNat = 128 / 2 ^ i * 4 := by
    rw [e₃, toNat_lsl_n (by rw [h₂.get .x11, h₁.get .x11, h.x11]; omega), h₂.get .x11, h₁.get .x11,
      h.x11]
  have l₀ : LInv s₀ ((nttLens.take i).foldl nttLayer (P₀ s₀)) (128 / 2 ^ i) u₃ 0 u₃ := by
    refine ⟨h.st.keep k₃ m₃, Keep.refl _ _, ?_, ?_, ?_, by rw [m₃, nttLayerN_zero]; exact h.poly⟩
    · rw [h₃.get .x2, h₂.get .x2, e₁, h.st.x0, Nat.mul_zero, Nat.mul_zero, ptr_zero]
    · rw [k₃.get .x12, h.x12, f1, Nat.add_zero]
    · rw [h₃.get .x16, e₂, h₁.get .x13, h.x13, f1, Nat.sub_zero]
  refine WP.seq (WP.mono (count_loop (n := 128 / (128 / 2 ^ i)) (by rw [f1]; exact Nat.two_pow_pos _)
    (LInv s₀ _ (128 / 2 ^ i) u₃) (fun b hb v hv => block_step hp f0 (by rw [f1]; omega)
      (by rw [f1]; omega) c11 c15 hb hv) l₀) fun u₄ h₄ => ?_)
  refine wp_lsr (by decide) fun u₅ h₅ e₅ => wp_add fun u₆ h₆ e₆ => wp_subImm (by decide)
    fun u₇ h₇ e₇ => wp_nil ?_
  have k₇ := (h₅.keep.trans h₆.keep).trans h₇.keep
  have c14 : (u₆.gpr .x14).toNat = 7 - i := by
    rw [h₆.get .x14, h₅.get .x14, h₄.keep.get .x14, k₃.get .x14, h.x14]
  have v14 : (u₇.gpr .x14).toNat = 7 - (i + 1) := by
    rw [e₇, toNat_sub_n (by rw [c14]; simp; omega), c14]
    simp
    omega
  have c13 : (u₅.gpr .x13).toNat = 2 ^ i := by
    rw [h₅.get .x13, h₄.keep.get .x13, k₃.get .x13, h.x13]
  refine ⟨⟨h₄.st.keep k₇ (by rw [h₇.mem, h₆.mem, h₅.mem]), ?_, ?_, ?_, v14, ?_⟩, by rw [v14]; omega⟩
  · rw [h₇.get .x11, h₆.get .x11, e₅, toNat_lsr, h₄.keep.get .x11, c11, ← f4]
  · rw [k₇.get .x12, h₄.x12, f1, show 2 ^ i + 2 ^ i = 2 ^ (i + 1) by rw [Nat.pow_succ]; omega]
  · rw [h₇.get .x13, e₆, toNat_add_n (by rw [c13]; omega), c13, Nat.pow_succ]
    omega
  · rw [h₇.mem, h₆.mem, h₅.mem, foldl_take_succ _ _ _ 0 (by rw [show nttLens.length = 7 from rfl]; exact hi),
      f5]
    exact h₄.poly

theorem correct (s₀ : State) (hs : (inPlaceAArch64 ntt).pre s₀) :
    ∃ t s', Exec isa Impl.MlKem.AArch64.ntt s₀ t s' ∧ abiPreserved s₀ s' ∧
      (inPlaceAArch64 ntt).post s₀ s' := by
  have hp := pre_of hs
  suffices h : WP isa Impl.MlKem.AArch64.ntt s₀ fun s' => s'.sp = s₀.sp ∧
      (inPlaceAArch64 ntt).post s₀ s' by
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
  have i₀ : OInv s₀ 0 s₆ := by
    refine ⟨⟨k₆.rd, k₆.wr, k₆.sp, k₆.get .x0, ?_, ?_, fun k hk => by rw [m₆]; exact h₁.tab k hk⟩,
      by rw [h₆.get .x11, h₅.get .x11, h₄.get .x11, e₃]; rfl, ?_,
      by rw [h₆.get .x13, e₅]; rfl, by rw [e₆]; rfl, ?_⟩
    · rw [h₆.get .x9, h₅.get .x9, h₄.get .x9, h₃.get .x9, e₉]
    · rw [h₆.get .x10, h₅.get .x10, h₄.get .x10, h₃.get .x10, e₁₀]
    · rw [h₆.get .x12, h₅.get .x12, e₄, h₃.get .x1, h₂.get .x1, h₁.keep.get .x1]
    · rw [m₆]
      exact polyIs_frame h₁.frame fr ⟨hp.red, rfl⟩
  refine WP.mono (count_loop (by decide) (OInv s₀) (fun i hi u h => layer_step hp hi h) i₀)
    fun s' h => ⟨h.st.sp, ?_⟩
  show PolyIs s'.mem (fP s₀) (ntt (P₀ s₀))
  rw [ntt_eq_layers]
  exact h.poly

theorem ct : ConstantTime isa (inPlaceAArch64 ntt).pre (inPlaceAArch64 ntt).pub
    Impl.MlKem.AArch64.ntt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ ⟨h0, h1, hsp⟩ => agree_of hsp (by simp [h0, h1])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem ntt_verified :
    Verified AArch64.target Impl.MlKem.AArch64.ntt (Spec.MlKem.nttContract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig,
      inPlaceAArch64, AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.Ntt
