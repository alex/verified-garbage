import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon
import Mathlib.Tactic.Set

/-!
# ML-KEM on AArch64: `vg_mlkem_ntt`

Four butterflies of a block in vectors (`vstep`), the `len / 4` of them of a
block (`block_step`), the blocks of a layer with `len ≥ 4` (`layer_step`), the
layer with `len = 2` two blocks at a time (`pair_step`), and the seven layers
(`ntt_eq_layers`).
-/

namespace VG.Proof.MlKem.AArch64.Ntt

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem

/-! ## Memory -/

theorem Pre.in16 {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {j : Nat} (hj : j + 4 ≤ 256) :
    InRegions s.wr (coeffAddr (fP s₀) j) 16 := by
  rw [h.wr, hp.wr]
  exact in_regions (List.mem_cons_self ..) (contains_off (by omega) (by decide))

theorem Pre.in16' {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {j : Nat} (hj : j + 4 ≤ 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (fP s₀) j) 16 := by
  rw [h.rd, hp.rd]; exact hp.in16 h hj

/-- After two stores into the polynomial at `f`, the facts that hold throughout. -/
theorem St.store2 {s₀ : State} (hp : Pre s₀) {w w' : State} (h : St s₀ w) (hk : Keep [] w w')
    (hv : w'.v = w.v) {j j' : Nat} (hj : j + 4 ≤ 256) (hj' : j' + 4 ≤ 256) {x y : BitVec 128}
    (hm : w'.mem = (w.mem.write (coeffAddr (fP s₀) j) 16 x).write (coeffAddr (fP s₀) j') 16 y) :
    St s₀ w' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp], by rw [hk.get .x0, h.x0],
    ⟨by rw [hv]; exact h.vc.q, by rw [hv]; exact h.vc.m⟩,
    hp.tab_write (by rw [hm]; exact frame16 (frame16 (Frame.refl _ _) hj _) hj' _) h.tab⟩

/-! ## Four butterflies -/

/-- After `u` vectors of four butterflies of the block from `start`. -/
structure IInv (s₀ : State) (P : Poly) (len k start : Nat) (s : State) (u : Nat) (w : State) : Prop where
  st : St s₀ w
  keep : Keep [.x2, .x3, .x5] s w
  z : Lanes (w.v .v18) fun _ => (zeta k).val
  x2 : w.gpr .x2 = coeffAddr (fP s₀) (start + 4 * u)
  x3 : w.gpr .x3 = coeffAddr (fP s₀) (start + len + 4 * u)
  x5 : (w.gpr .x5).toNat = len / 4 - u
  poly : PolyIs w.mem (fP s₀) (nttBlockN P len k start (4 * u))

theorem vstep {s₀ : State} (hp : Pre s₀) {P : Poly} {len k start : Nat} (hs : start + 2 * len ≤ 256)
    {s : State} {u : Nat} (hu : 4 * u + 4 ≤ len) {w : State} (h : IInv s₀ P len k start s u w) :
    WP isa (.block (vBody (vbfly .v18))) w fun w' => IInv s₀ P len k start s (u + 1) w' ∧
      ((w'.gpr .x5).toNat ≠ 0 ↔ u + 1 ≠ len / 4) := by
  have hj : start + 4 * u + 4 ≤ 256 := by omega
  have hj' : start + len + 4 * u + 4 ≤ 256 := by omega
  simp only [vBody, List.cons_append, List.nil_append]
  refine wp_ldrq (a := coeffAddr (fP s₀) (start + 4 * u)) (by decide) (by rw [h.x2, ptr_zero])
    (hp.in16' h.st hj) fun w₁ h₁ => ?_
  refine wp_ldrq (a := coeffAddr (fP s₀) (start + len + 4 * u)) (by decide) (by rw [h₁.gpr, h.x3, ptr_zero])
    (by rw [h₁.rd, h₁.wr]; exact hp.in16' h.st hj') fun w₂ h₂ => ?_
  have la : Lanes (w₂.v .v0) fun e => ((nttBlockN P len k start (4 * u))[start + 4 * u + e]!).val := by
    rw [h₂.get .v0, h₁.v]; exact lanes_load h.poly hj
  have lb : Lanes (w₂.v .v1) fun e =>
      ((nttBlockN P len k start (4 * u))[start + len + 4 * u + e]!).val := by
    rw [h₂.v, h₁.mem]; exact lanes_load h.poly hj'
  have lz : Lanes (w₂.v .v18) fun _ => (zeta k).val := by rw [h₂.get .v18, h₁.get .v18]; exact h.z
  have st₂ := h.st.vchg (h₁.chg.trans h₂.chg)
  refine vbfly_ok st₂.vc la (fun _ _ => val_lt _) lb (fun _ _ => val_lt _) lz (fun _ _ => val_lt _)
    fun w₃ h₃ l2 l1 => ?_
  have st₃ := st₂.vchg h₃
  refine wp_strq (a := coeffAddr (fP s₀) (start + 4 * u)) (by decide)
    (by rw [h₃.gpr, h₂.gpr, h₁.gpr, h.x2, ptr_zero]) (hp.in16 st₃ hj) fun w₄ h₄ => ?_
  refine wp_strq (a := coeffAddr (fP s₀) (start + len + 4 * u)) (by decide)
    (by rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, h.x3, ptr_zero]) (by rw [h₄.wr]; exact hp.in16 st₃ hj')
    fun w₅ h₅ => ?_
  have m₅ : w₅.mem = (w₃.mem.write (coeffAddr (fP s₀) (start + 4 * u)) 16 (w₃.v .v2)).write
      (coeffAddr (fP s₀) (start + len + 4 * u)) 16 (w₃.v .v1) := by
    rw [h₅.mem, h₄.v, h₄.mem]
  have st₅ : St s₀ w₅ := St.store2 hp st₃ (h₄.keep.trans h₅.keep).mono (by rw [h₅.v, h₄.v]) hj hj' m₅
  have mw : w₃.mem = w.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  -- the pointers and the count
  refine WP.mono (WP.keepV (Q := fun w' => Keep [.x2, .x3, .x5] w₅ w' ∧ w'.mem = w₅.mem ∧
      w'.gpr .x2 = w₅.gpr .x2 + BitVec.ofNat 64 16 ∧ w'.gpr .x3 = w₅.gpr .x3 + BitVec.ofNat 64 16 ∧
      w'.gpr .x5 = w₅.gpr .x5 - BitVec.ofNat 64 1) (by decide)
    (wp_addImm (by decide) fun w₆ h₆ e₆ => wp_addImm (by decide) fun w₇ h₇ e₇ =>
      wp_subImm (by decide) fun w₈ h₈ e₈ => wp_nil ⟨((h₆.keep.trans h₇.keep).trans h₈.keep).mono,
        by rw [h₈.mem, h₇.mem, h₆.mem], by rw [h₈.get .x2, h₇.get .x2, e₆],
        by rw [h₈.get .x3, e₇, h₆.get .x3], by rw [e₈, h₇.get .x5, h₆.get .x5]⟩))
    fun w' ⟨⟨k', m', e2, e3, e5⟩, hv⟩ => ?_
  have g₅ : w₅.gpr = w.gpr := by rw [h₅.gpr, h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr]
  have c5 : (w₅.gpr .x5).toNat = len / 4 - u := by rw [g₅, h.x5]
  have x5' : (w'.gpr .x5).toNat = len / 4 - (u + 1) := by
    rw [e5, toNat_sub_n (by rw [c5]; simp; omega), c5]; simp; omega
  refine ⟨⟨st₅.keep k' m' hv, ?_, ?_, ?_, ?_, x5', ?_⟩, by rw [x5']; omega⟩
  · exact (h.keep.trans ((((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans
      h₅.keep).trans k'))).mono
  · rw [hv, h₅.v, h₄.v, h₃.get .v18, h₂.get .v18, h₁.get .v18]; exact h.z
  · rw [e2, g₅, h.x2, coeffAddr_step, show start + 4 * u + 4 = start + 4 * (u + 1) by omega]
  · rw [e3, g₅, h.x3, coeffAddr_step, show start + len + 4 * u + 4 = start + len + 4 * (u + 1) by omega]
  · rw [m', m₅, mw]
    refine polyIs_write16x2 h.poly hj hj' (by omega)
      (a := fun e => (nttBlockN P len k start (4 * u))[start + 4 * u + e]! +
        zeta k * (nttBlockN P len k start (4 * u))[start + len + 4 * u + e]!)
      (b := fun e => (nttBlockN P len k start (4 * u))[start + 4 * u + e]! -
        zeta k * (nttBlockN P len k start (4 * u))[start + len + 4 * u + e]!)
      (l2.congr fun e he => ?_) (l1.congr fun e he => ?_) fun i hi => ?_
    · rw [val_add', val_mul, Nat.mul_comm (zeta k).val]
    · rw [val_sub', val_mul, Nat.mul_comm (zeta k).val]
    · rw [show 4 * (u + 1) = 4 * u + 4 by omega, nttBlockN_add,
        nttBlockN_get' _ (by omega) (by omega) (by rw [n_eq]; omega) (by rw [n_eq]; exact hi)]
      by_cases c1 : start + 4 * u ≤ i ∧ i < start + 4 * u + 4
      · rw [ite_eq_left c1, ite_eq_left c1, show start + 4 * u + (i - (start + 4 * u)) = i by omega,
          show start + len + 4 * u + (i - (start + 4 * u)) = i + len by omega]
      · rw [ite_eq_right c1, ite_eq_right c1]
        by_cases c2 : start + 4 * u + len ≤ i ∧ i < start + 4 * u + len + 4
        · rw [ite_eq_left c2, ite_eq_left (by omega),
            show start + 4 * u + (i - (start + len + 4 * u)) = i - len by omega,
            show start + len + 4 * u + (i - (start + len + 4 * u)) = i by omega]
        · rw [ite_eq_right c2, ite_eq_right (by omega)]

/-! ## A block, and a layer with `len ≥ 4` -/

/-- The registers a block changes. -/
abbrev kRegs : List Reg := [.x2, .x3, .x5, .x12, .x16, .x17]

/-- After `b` blocks of the layer with `len`. -/
structure LInv (s₀ : State) (P : Poly) (len : Nat) (L : State) (b : Nat) (u : State) : Prop where
  st : St s₀ u
  keep : Keep kRegs L u
  x2 : u.gpr .x2 = fP s₀ + BitVec.ofNat 64 (4 * (2 * len * b))
  x12 : u.gpr .x12 = sP s₀ + BitVec.ofNat 64 (4 * (128 / len + b))
  x16 : (u.gpr .x16).toNat = 128 / len - b
  poly : PolyIs u.mem (fP s₀) (nttLayerN P len b)

theorem lanes_zeta {s₀ s : State} (h : St s₀ s) {k : Nat} (hk : k < 128) :
    Lanes (ofVWords (((s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 32).setWidth 64).setWidth 32)
      (((s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 32).setWidth 64).setWidth 32)
      (((s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 32).setWidth 64).setWidth 32)
      (((s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 32).setWidth 64).setWidth 32))
      fun _ => (zeta k).val :=
  lanes_dup.congr fun _ _ => by
    rw [BitVec.toNat_setWidth, zeta_load h hk, Nat.mod_eq_of_lt (by have := val_lt (zeta k); omega)]

/-- One block. -/
theorem block_step {s₀ : State} (hp : Pre s₀) {P : Poly} {len : Nat} (h4 : 4 ≤ len) (hl4 : len % 4 = 0)
    (hnb : len * (128 / len) = 128) (hk : 2 * (128 / len) ≤ 128) {L : State}
    (h11 : (L.gpr .x11).toNat = len / 4) (h15 : (L.gpr .x15).toNat = len * 4) {b : Nat}
    (hb : b < 128 / len) {u : State} (h : LInv s₀ P len L b u) :
    WP isa (vBlockCode (vbfly .v18) [.addImm .x .x12 .x12 4]) u fun u' => LInv s₀ P len L (b + 1) u' ∧
      ((u'.gpr .x16).toNat ≠ 0 ↔ b + 1 ≠ 128 / len) := by
  have hbl : 2 * len * b + 2 * len ≤ 256 := by
    have : len * (b + 1) ≤ len * (128 / len) := Nat.mul_le_mul_left _ hb
    rw [Nat.mul_succ] at this
    rw [Nat.mul_assoc]
    omega
  have hk' : 128 / len + b < 128 := by omega
  refine WP.seq ?_
  show WP isa (.block ([Instr.ldr .w .x17 .x12 0, .addImm .x .x12 .x12 4] ++
    (.vop (.dup .s4 .v18 .x17) :: (([.add .x .x3 .x2 .x15, mov .x5 .x11] : List Instr) ++ [])))) u _
  refine wp_scalar (by decide) (P := fun u₂ => Keep [.x17, .x12] u u₂ ∧ u₂.mem = u.mem ∧
      u₂.gpr .x17 = (u.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * (128 / len + b))) 32).setWidth 64 ∧
      u₂.gpr .x12 = u.gpr .x12 + BitVec.ofNat 64 4)
    (wp_ldrw (a := sP s₀ + BitVec.ofNat 64 (4 * (128 / len + b))) (by decide) (by rw [h.x12, ptr_zero])
      (hp.in_tab h.st hk') fun u₁ h₁ e₁ => wp_addImm (by decide) fun u₂ h₂ e₂ =>
        wp_nil ⟨(h₁.keep.trans h₂.keep).mono, by rw [h₂.mem, h₁.mem], by rw [h₂.get .x17, e₁],
          by rw [e₂, h₁.get .x12]⟩) fun u₂ ⟨k₂, m₂, e17, e12⟩ hv₂ => ?_
  have st₂ := h.st.keep k₂ m₂ hv₂
  refine wp_vop (d := .v18) rfl fun u₃ h₃ => ?_
  have st₃ := st₂.vchg h₃.chg
  refine wp_scalar (by decide) (P := fun u₄ => Keep [.x3, .x5] u₃ u₄ ∧ u₄.mem = u₃.mem ∧
      u₄.gpr .x3 = u₃.gpr .x2 + u₃.gpr .x15 ∧ u₄.gpr .x5 = u₃.gpr .x11)
    (wp_add fun u₄ h₄ e₄ => wp_mov fun u₅ h₅ e₅ => wp_nil ⟨(h₄.keep.trans h₅.keep).mono,
      by rw [h₅.mem, h₄.mem], by rw [h₅.get .x3, e₄], by rw [e₅, h₄.get .x11]⟩)
    fun u₄ ⟨k₄, m₄, e3, e5⟩ hv₄ => wp_nil ?_
  have st₄ := st₃.keep k₄ m₄ hv₄
  have g₃ : u₃.gpr = u₂.gpr := h₃.gpr
  have z₄ : Lanes (u₄.v .v18) fun _ => (zeta (128 / len + b)).val := by
    rw [hv₄, h₃.v, e17, ← m₂]; exact lanes_zeta st₂ hk'
  have i₀ : IInv s₀ (nttLayerN P len b) len (128 / len + b) (2 * len * b) u₄ 0 u₄ := by
    refine ⟨st₄, Keep.refl _ _, z₄, ?_, ?_, ?_, ?_⟩
    · rw [k₄.get .x2, g₃, k₂.get .x2, h.x2, coeffAddr, Nat.mul_zero, Nat.add_zero]
    · have e15 : u₃.gpr .x15 = BitVec.ofNat 64 (len * 4) := by
        apply BitVec.eq_of_toNat_eq
        rw [g₃, k₂.get .x15, h.keep.get .x15, h15, toNat_ofNat_lt (by omega)]
      rw [e3, g₃, k₂.get .x2, h.x2, ← g₃, e15, ptr_add, coeffAddr, Nat.mul_zero, Nat.add_zero]
      congr 2; rw [Nat.mul_comm len 4, Nat.mul_add]
    · rw [e5, g₃, k₂.get .x11, h.keep.get .x11, h11, Nat.sub_zero]
    · rw [m₄, h₃.mem, m₂, nttBlockN_zero]; exact h.poly
  refine WP.seq (WP.mono (count_loop (n := len / 4) (by omega) (IInv s₀ (nttLayerN P len b) len
    (128 / len + b) (2 * len * b) u₄) (fun t ht w hw => vstep hp hbl (by omega) hw) i₀) fun u₅ h₅ => ?_)
  show WP isa (.block ([mov .x2 .x3, .subImm .x .x16 .x16 1] ++ [])) u₅ _
  refine wp_scalar (by decide) (P := fun u₇ => Keep [.x2, .x16] u₅ u₇ ∧ u₇.mem = u₅.mem ∧
      u₇.gpr .x2 = u₅.gpr .x3 ∧ u₇.gpr .x16 = u₅.gpr .x16 - BitVec.ofNat 64 1)
    (wp_mov fun u₆ h₆ e₆ => wp_subImm (by decide) fun u₇ h₇ e₇ => wp_nil ⟨(h₆.keep.trans h₇.keep).mono,
      by rw [h₇.mem, h₆.mem], by rw [h₇.get .x2, e₆], by rw [e₇, h₆.get .x16]⟩)
    fun u₇ ⟨k₇, m₇, e2, e16⟩ hv₇ => wp_nil ?_
  have k₅ := ((((h.keep.trans k₂).trans h₃.keep).trans k₄).trans h₅.keep)
  have c16 : (u₅.gpr .x16).toNat = 128 / len - b := by
    rw [h₅.keep.get .x16, k₄.get .x16, g₃, k₂.get .x16, h.x16]
  have v16 : (u₇.gpr .x16).toNat = 128 / len - (b + 1) := by
    rw [e16, toNat_sub_n (by rw [c16]; simp; omega), c16]
    simp
    omega
  refine ⟨⟨h₅.st.keep k₇ m₇ hv₇, (k₅.trans k₇).mono, ?_, ?_, v16, ?_⟩, by rw [v16]; omega⟩
  · rw [e2, h₅.x3, coeffAddr, show 2 * len * b + len + 4 * (len / 4) = 2 * len * (b + 1) by
      rw [Nat.mul_succ]; omega]
  · rw [k₇.get .x12, h₅.keep.get .x12, k₄.get .x12, g₃, e12, h.x12, ptr_next]
    rfl
  · have p₅ := h₅.poly
    rw [show 4 * (len / 4) = len by omega] at p₅
    rw [m₇, nttLayerN_succ, nttBlock]
    exact p₅

theorem foldl_take_succ {α β : Type} (g : α → β → α) (x : α) (L : List β) (d : β) {i : Nat}
    (hi : i < L.length) : (L.take (i + 1)).foldl g x = g ((L.take i).foldl g x) (L.getD i d) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.foldl_append, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi]
  rfl

/-- The layers with `len ≥ 4`: `len = 128 / 2ⁱ`, `2ⁱ` blocks. -/
theorem lfacts : ∀ i < 6, (4 : Nat) ≤ 128 / 2 ^ i ∧ (128 / 2 ^ i % 4 : Nat) = 0 ∧
    (128 / (128 / 2 ^ i) : Nat) = 2 ^ i ∧ (128 / 2 ^ i * 2 ^ i : Nat) = 128 ∧ (2 ^ i : Nat) ≤ 32 ∧
    (32 / 2 ^ i / 2 : Nat) = 32 / 2 ^ (i + 1) ∧ nttLens.getD i 0 = 128 / 2 ^ i ∧
    (128 / 2 ^ i / 4 : Nat) = 32 / 2 ^ i ∧ (128 / 2 ^ i : Nat) ≤ 128 := by
  decide +kernel

/-- After `i` layers. -/
structure OInv (s₀ : State) (i : Nat) (u : State) : Prop where
  st : St s₀ u
  x11 : (u.gpr .x11).toNat = 32 / 2 ^ i
  x12 : u.gpr .x12 = sP s₀ + BitVec.ofNat 64 (4 * 2 ^ i)
  x13 : (u.gpr .x13).toNat = 2 ^ i
  x14 : (u.gpr .x14).toNat = 6 - i
  poly : PolyIs u.mem (fP s₀) ((nttLens.take i).foldl nttLayer (P₀ s₀))

/-- One layer with `len ≥ 4`. -/
theorem layer_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 6) {u : State} (h : OInv s₀ i u) :
    WP isa nttLayerCode u fun u' => OInv s₀ (i + 1) u' ∧ ((u'.gpr .x14).toNat ≠ 0 ↔ i + 1 ≠ 6) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := lfacts i hi
  refine WP.seq ?_
  show WP isa (.block ([mov .x2 .x0, mov .x16 .x13, .lsl .x .x15 .x11 4] ++ [])) u _
  refine wp_scalar (by decide) (P := fun u₃ => Keep [.x2, .x16, .x15] u u₃ ∧ u₃.mem = u.mem ∧
      u₃.gpr .x2 = u.gpr .x0 ∧ u₃.gpr .x16 = u.gpr .x13 ∧ u₃.gpr .x15 = u.gpr .x11 <<< 4)
    (wp_mov fun u₁ h₁ e₁ => wp_mov fun u₂ h₂ e₂ => wp_lsl (by decide) fun u₃ h₃ e₃ =>
      wp_nil ⟨((h₁.keep.trans h₂.keep).trans h₃.keep).mono, by rw [h₃.mem, h₂.mem, h₁.mem],
        by rw [h₃.get .x2, h₂.get .x2, e₁], by rw [h₃.get .x16, e₂, h₁.get .x13],
        by rw [e₃, h₂.get .x11, h₁.get .x11]⟩) fun u₃ ⟨k₃, m₃, e2, e16, e15⟩ hv₃ => wp_nil ?_
  have c11 : (u₃.gpr .x11).toNat = 128 / 2 ^ i / 4 := by rw [k₃.get .x11, h.x11, f7]
  have c15 : (u₃.gpr .x15).toNat = 128 / 2 ^ i * 4 := by
    rw [e15, toNat_lsl_n (by rw [h.x11]; omega), h.x11]; omega
  have l₀ : LInv s₀ ((nttLens.take i).foldl nttLayer (P₀ s₀)) (128 / 2 ^ i) u₃ 0 u₃ := by
    refine ⟨h.st.keep k₃ m₃ hv₃, Keep.refl _ _, ?_, ?_, ?_, by rw [m₃, nttLayerN_zero]; exact h.poly⟩
    · rw [e2, h.st.x0, Nat.mul_zero, Nat.mul_zero, ptr_zero]
    · rw [k₃.get .x12, h.x12, f2, Nat.add_zero]
    · rw [e16, h.x13, f2, Nat.sub_zero]
  refine WP.seq (WP.mono (count_loop (n := 128 / (128 / 2 ^ i)) (by rw [f2]; exact Nat.two_pow_pos _)
    (LInv s₀ _ (128 / 2 ^ i) u₃) (fun b hb v hv => block_step hp f0 f1 (by rw [f2]; omega)
      (by rw [f2]; omega) c11 c15 hb hv) l₀) fun u₄ h₄ => ?_)
  show WP isa (.block (([.lsr .x .x11 .x11 1, .add .x .x13 .x13 .x13, .subImm .x .x14 .x14 1] : List Instr) ++ [])) u₄ _
  refine wp_scalar (by decide) (P := fun u₇ => Keep [.x11, .x13, .x14] u₄ u₇ ∧ u₇.mem = u₄.mem ∧
      u₇.gpr .x11 = u₄.gpr .x11 >>> 1 ∧ u₇.gpr .x13 = u₄.gpr .x13 + u₄.gpr .x13 ∧
      u₇.gpr .x14 = u₄.gpr .x14 - BitVec.ofNat 64 1)
    (wp_lsr (by decide) fun u₅ h₅ e₅ => wp_add fun u₆ h₆ e₆ => wp_subImm (by decide) fun u₇ h₇ e₇ =>
      wp_nil ⟨((h₅.keep.trans h₆.keep).trans h₇.keep).mono, by rw [h₇.mem, h₆.mem, h₅.mem],
        by rw [h₇.get .x11, h₆.get .x11, e₅], by rw [h₇.get .x13, e₆, h₅.get .x13],
        by rw [e₇, h₆.get .x14, h₅.get .x14]⟩) fun u₇ ⟨k₇, m₇, e11, e13, e14⟩ hv₇ => wp_nil ?_
  have c14 : (u₄.gpr .x14).toNat = 6 - i := by rw [h₄.keep.get .x14, k₃.get .x14, h.x14]
  have v14 : (u₇.gpr .x14).toNat = 6 - (i + 1) := by
    rw [e14, toNat_sub_n (by rw [c14]; simp; omega), c14]
    simp
    omega
  have c13 : (u₄.gpr .x13).toNat = 2 ^ i := by rw [h₄.keep.get .x13, k₃.get .x13, h.x13]
  refine ⟨⟨h₄.st.keep k₇ m₇ hv₇, ?_, ?_, ?_, v14, ?_⟩, by rw [v14]; omega⟩
  · rw [e11, toNat_lsr, h₄.keep.get .x11, k₃.get .x11, h.x11, ← f5]
  · rw [k₇.get .x12, h₄.x12, f2, show 2 ^ i + 2 ^ i = 2 ^ (i + 1) by rw [Nat.pow_succ]; omega]
  · rw [e13, toNat_add_n (by rw [c13]; omega), c13, Nat.pow_succ]
    omega
  · rw [m₇, foldl_take_succ _ _ _ 0 (by rw [show nttLens.length = 7 from rfl]; omega), f6]
    exact h₄.poly

/-! ## The layer with `len = 2` -/

theorem ntt_eq_last (f : Poly) :
    nttLens.foldl nttLayer f = nttLayer ((nttLens.take 6).foldl nttLayer f) 2 := by
  have h := foldl_take_succ nttLayer f nttLens 0 (i := 6) (by decide)
  rw [show nttLens.take 7 = nttLens from rfl, show nttLens.getD 6 0 = 2 from rfl] at h
  exact h

/-- The zetas `k` and `k + 1` loaded as a pair, and spread over the lanes as
`(ζ_k, ζ_k, ζ_{k+1}, ζ_{k+1})`. -/
theorem lanes_zpair {s₀ s : State} (h : St s₀ s) {k : Nat} (hk : k + 1 < 128) :
    Lanes (VPermOp.eval .zip1 .s4
      (ofVDwords (s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 64)
        (s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 64))
      (ofVDwords (s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 64)
        (s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 64)))
      fun e => (zeta (k + e / 2)).val := fun e he => by
  show _ = (zeta (k + e / 2)).val
  rw [vword_zip1_s4 _ he, vword_dup_d2 _ (by omega)]
  have t : ∀ j, j < 128 → ((s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * j)) 32)).toNat = (zeta j).val :=
    fun j hj => by
      rw [h.tab j hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
          have := zetaTable_lt j hj; have hq : q = 3329 := rfl; omega),
        zetaTable_zeta hj]
  rcases (show e / 2 = 0 ∨ e / 2 = 1 by omega) with e2 | e2 <;> rw [e2]
  · rw [Nat.zero_mod, Nat.mul_zero, readW64_lo, Nat.add_zero]; exact t k (by omega)
  · rw [show 1 % 2 = 1 from rfl, Nat.mul_one, readW64_hi, ptr_add, show 4 * k + 4 = 4 * (k + 1) by omega]
    exact t (k + 1) hk

/-- After `c` pairs of the blocks of the layer with `len = 2`. -/
structure PInv (s₀ : State) (R : Poly) (c : Nat) (w : State) : Prop where
  st : St s₀ w
  x2 : w.gpr .x2 = coeffAddr (fP s₀) (8 * c)
  x12 : w.gpr .x12 = sP s₀ + BitVec.ofNat 64 (4 * (64 + 2 * c))
  x5 : (w.gpr .x5).toNat = 32 - c
  poly : PolyIs w.mem (fP s₀) (nttLayerN R 2 (2 * c))

/-- The coefficients after the pair `c` of blocks of the layer with `len = 2`. -/
theorem pair_poly (R : Poly) {c : Nat} (hc : c < 32) : ∀ i < 256, (nttLayerN R 2 (2 * (c + 1)))[i]! =
    if 8 * c ≤ i ∧ i < 8 * c + 4 then
      (fun e => if e < 2 then (nttLayerN R 2 (2 * c))[8 * c + e]! +
          zeta (64 + 2 * c) * (nttLayerN R 2 (2 * c))[8 * c + e + 2]!
        else (nttLayerN R 2 (2 * c))[8 * c + e - 2]! - zeta (64 + 2 * c) * (nttLayerN R 2 (2 * c))[8 * c + e]!)
        (i - 8 * c)
    else if 8 * c + 4 ≤ i ∧ i < 8 * c + 4 + 4 then
      (fun e => if e < 2 then (nttLayerN R 2 (2 * c))[8 * c + 4 + e]! +
          zeta (64 + 2 * c + 1) * (nttLayerN R 2 (2 * c))[8 * c + 4 + e + 2]!
        else (nttLayerN R 2 (2 * c))[8 * c + 4 + e - 2]! -
          zeta (64 + 2 * c + 1) * (nttLayerN R 2 (2 * c))[8 * c + 4 + e]!)
        (i - (8 * c + 4))
    else (nttLayerN R 2 (2 * c))[i]! := by
  intro i hi
  set P' := nttLayerN R 2 (2 * c)
  have hn : i < n := by rw [n_eq]; exact hi
  rw [show 2 * (c + 1) = 2 * c + 1 + 1 by omega, nttLayerN_succ, nttLayerN_succ,
    nttBlock_get _ (by decide) (by rw [n_eq]; omega) hn,
    show 128 / 2 + (2 * c + 1) = 64 + 2 * c + 1 by omega, show 2 * 2 * (2 * c + 1) = 8 * c + 4 by omega]
  have Qg : ∀ x < 256, (nttBlock P' 2 (128 / 2 + 2 * c) (2 * 2 * (2 * c)))[x]! =
      if 8 * c ≤ x ∧ x < 8 * c + 2 then P'[x]! + zeta (64 + 2 * c) * P'[x + 2]!
      else if 8 * c + 2 ≤ x ∧ x < 8 * c + 4 then P'[x - 2]! - zeta (64 + 2 * c) * P'[x]!
      else P'[x]! := fun x hx => by
    rw [nttBlock_get _ (by decide) (by rw [n_eq]; omega) (by rw [n_eq]; exact hx),
      show 128 / 2 + 2 * c = 64 + 2 * c by omega, show 2 * 2 * (2 * c) = 8 * c by omega]
  rcases (by omega : i < 8 * c ∨ (8 * c ≤ i ∧ i < 8 * c + 2) ∨ (8 * c + 2 ≤ i ∧ i < 8 * c + 4) ∨
      (8 * c + 4 ≤ i ∧ i < 8 * c + 6) ∨ (8 * c + 6 ≤ i ∧ i < 8 * c + 8) ∨ 8 * c + 8 ≤ i) with
    h | h | h | h | h | h
  · rw [Qg i hi]
    simp (disch := omega) only [ite_eq_left, ite_eq_right]
  · rw [Qg i hi]
    simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_of_le]
  · rw [Qg i hi]
    simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_of_le]
  · rw [Qg i hi, Qg (i + 2) (by omega)]
    simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_of_le]
  · rw [Qg i hi, Qg (i - 2) (by omega)]
    simp (disch := omega) only [ite_eq_left, ite_eq_right, Nat.add_sub_of_le]
  · rw [Qg i hi]
    simp (disch := omega) only [ite_eq_left, ite_eq_right]

theorem pair_step {s₀ : State} (hp : Pre s₀) {R : Poly} {c : Nat} (hc : c < 32) {w : State}
    (h : PInv s₀ R c w) :
    WP isa (.block (vPairBody (vbfly .v18) false [.addImm .x .x12 .x12 8])) w fun w' =>
      PInv s₀ R (c + 1) w' ∧ ((w'.gpr .x5).toNat ≠ 0 ↔ c + 1 ≠ 32) := by
  show WP isa (.block (([.ldr .x .x17 .x12 0, .addImm .x .x12 .x12 8] : List Instr) ++
    ((.vop (.dup .d2 .v19 .x17) :: .vop (.perm .zip1 .s4 .v18 .v19 .v19) :: .ldrq .v5 .x2 0 ::
      .ldrq .v6 .x2 16 :: .vop (.perm .trn1 .d2 .v0 .v5 .v6) :: .vop (.perm .trn2 .d2 .v1 .v5 .v6) ::
      (vbfly .v18 ++ ((.vop (.perm .trn1 .d2 .v5 .v2 .v1) :: .vop (.perm .trn2 .d2 .v6 .v2 .v1) ::
        .strq .v5 .x2 0 :: .strq .v6 .x2 16 ::
        (([.addImm .x .x2 .x2 32, .subImm .x .x5 .x5 1] : List Instr) ++ ([] : List Instr))) : List Instr))) :
      List Instr))) w _
  have hk : 4 * (64 + 2 * c) + 8 ≤ 1024 := by omega
  refine wp_scalar (by decide) (P := fun w₂ => Keep [.x17, .x12] w w₂ ∧ w₂.mem = w.mem ∧
      w₂.gpr .x17 = w.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * (64 + 2 * c))) 64 ∧
      w₂.gpr .x12 = w.gpr .x12 + BitVec.ofNat 64 8)
    (wp_ldrx (a := sP s₀ + BitVec.ofNat 64 (4 * (64 + 2 * c))) (by decide) (by rw [h.x12, ptr_zero])
      (by rw [h.st.rd, h.st.wr, hp.rd, hp.wr]
          exact in_regions (R := polyRegion (sP s₀)) (by simp) (contains_off hk (by decide)))
      fun w₁ h₁ e₁ => wp_addImm (by decide) fun w₂ h₂ e₂ =>
        wp_nil ⟨(h₁.keep.trans h₂.keep).mono, by rw [h₂.mem, h₁.mem], by rw [h₂.get .x17, e₁],
          by rw [e₂, h₁.get .x12]⟩) fun w₂ ⟨k₂, m₂, e17, e12⟩ hv₂ => ?_
  have st₂ := h.st.keep k₂ m₂ hv₂
  refine wp_vop (d := .v19) rfl fun w₃ h₃ => wp_vop (d := .v18) rfl fun w₄ h₄ => ?_
  have lz : Lanes (w₄.v .v18) fun e => (zeta (64 + 2 * c + e / 2)).val := by
    rw [h₄.v, h₃.v, e17, ← m₂]; exact lanes_zpair st₂ (by omega)
  have hj : 8 * c + 4 ≤ 256 := by omega
  have hj' : 8 * c + 4 + 4 ≤ 256 := by omega
  have g₄ : w₄.gpr = w₂.gpr := by rw [h₄.gpr, h₃.gpr]
  have mw₄ : w₄.mem = w.mem := by rw [h₄.mem, h₃.mem, m₂]
  refine wp_ldrq (a := coeffAddr (fP s₀) (8 * c)) (by decide) (by rw [g₄, k₂.get .x2, h.x2, ptr_zero])
    (by rw [h₄.rd, h₃.rd, h₄.wr, h₃.wr]; exact hp.in16' st₂ hj) fun w₅ h₅ => ?_
  refine wp_ldrq (a := coeffAddr (fP s₀) (8 * c + 4)) (by decide)
    (by rw [h₅.gpr, g₄, k₂.get .x2, h.x2, coeffAddr_step])
    (by rw [h₅.rd, h₅.wr, h₄.rd, h₄.wr, h₃.rd, h₃.wr]; exact hp.in16' st₂ hj') fun w₆ h₆ => ?_
  have l5 : Lanes (w₆.v .v5) fun e => ((nttLayerN R 2 (2 * c))[8 * c + e]!).val := by
    rw [h₆.get .v5, h₅.v, mw₄]; exact lanes_load h.poly hj
  have l6 : Lanes (w₆.v .v6) fun e => ((nttLayerN R 2 (2 * c))[8 * c + 4 + e]!).val := by
    rw [h₆.v, h₅.mem, mw₄]; exact lanes_load h.poly hj'
  refine wp_vop (d := .v0) rfl fun w₇ h₇ => wp_vop (d := .v1) rfl fun w₈ h₈ => ?_
  -- the pairs gathered: `v0 = (f[0], f[1], f[4], f[5])`, `v1 = (f[2], f[3], f[6], f[7])`
  have lA : Lanes (w₈.v .v0) fun e => ((nttLayerN R 2 (2 * c))[8 * c + e + 2 * (e / 2)]!).val :=
    fun e he => by
      show _ = ((nttLayerN R 2 (2 * c))[8 * c + e + 2 * (e / 2)]!).val
      rw [h₈.get .v0, h₇.v, vword_trn1_d2 _ _ he]
      rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl
      · exact l5 0 (by decide)
      · exact l5 1 (by decide)
      · exact l6 0 (by decide)
      · exact l6 1 (by decide)
  have lB : Lanes (w₈.v .v1) fun e => ((nttLayerN R 2 (2 * c))[8 * c + e + 2 * (e / 2) + 2]!).val :=
    fun e he => by
      show _ = ((nttLayerN R 2 (2 * c))[8 * c + e + 2 * (e / 2) + 2]!).val
      rw [h₈.v, h₇.get .v5, h₇.get .v6, vword_trn2_d2 _ _ he]
      rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl
      · exact l5 2 (by decide)
      · exact l5 3 (by decide)
      · exact l6 2 (by decide)
      · exact l6 3 (by decide)
  have lZ : Lanes (w₈.v .v18) fun e => (zeta (64 + 2 * c + e / 2)).val := by
    rw [h₈.get .v18, h₇.get .v18, h₆.get .v18, h₅.get .v18]; exact lz
  have st₈ := st₂.vchg ((((((h₃.chg.trans h₄.chg).trans h₅.chg).trans h₆.chg).trans h₇.chg).trans
    h₈.chg))
  refine vbfly_ok st₈.vc lA (fun _ _ => val_lt _) lB (fun _ _ => val_lt _) lZ (fun _ _ => val_lt _)
    fun w₉ h₉ l2 l1 => ?_
  refine wp_vop (d := .v5) rfl fun w₁₀ h₁₀ => wp_vop (d := .v6) rfl fun w₁₁ h₁₁ => ?_
  have st₁₁ := st₈.vchg ((h₉.trans h₁₀.chg).trans h₁₁.chg)
  have g₁₁ : w₁₁.gpr = w₂.gpr := by
    rw [h₁₁.gpr, h₁₀.gpr, h₉.gpr, h₈.gpr, h₇.gpr, h₆.gpr, h₅.gpr, h₄.gpr, h₃.gpr]
  refine wp_strq (a := coeffAddr (fP s₀) (8 * c)) (by decide) (by rw [g₁₁, k₂.get .x2, h.x2, ptr_zero])
    (hp.in16 st₁₁ hj) fun w₁₂ h₁₂ => ?_
  refine wp_strq (a := coeffAddr (fP s₀) (8 * c + 4)) (by decide)
    (by rw [h₁₂.gpr, g₁₁, k₂.get .x2, h.x2, coeffAddr_step]) (by rw [h₁₂.wr]; exact hp.in16 st₁₁ hj')
    fun w₁₃ h₁₃ => ?_
  have m₁₃ : w₁₃.mem = (w₁₁.mem.write (coeffAddr (fP s₀) (8 * c)) 16 (w₁₁.v .v5)).write
      (coeffAddr (fP s₀) (8 * c + 4)) 16 (w₁₁.v .v6) := by
    rw [h₁₃.mem, h₁₂.v, h₁₂.mem]
  have st₁₃ : St s₀ w₁₃ := St.store2 hp st₁₁ (h₁₂.keep.trans h₁₃.keep).mono (by rw [h₁₃.v, h₁₂.v]) hj hj' m₁₃
  have mw : w₁₁.mem = w.mem := by
    rw [h₁₁.mem, h₁₀.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, mw₄]
  refine WP.mono (WP.keepV (Q := fun w' => Keep [.x2, .x5] w₁₃ w' ∧ w'.mem = w₁₃.mem ∧
      w'.gpr .x2 = w₁₃.gpr .x2 + BitVec.ofNat 64 32 ∧ w'.gpr .x5 = w₁₃.gpr .x5 - BitVec.ofNat 64 1)
      (by decide)
    (wp_addImm (by decide) fun w₁₄ h₁₄ e₁₄ => wp_subImm (by decide) fun w₁₅ h₁₅ e₁₅ =>
      wp_nil ⟨(h₁₄.keep.trans h₁₅.keep).mono, by rw [h₁₅.mem, h₁₄.mem], by rw [h₁₅.get .x2, e₁₄],
        by rw [e₁₅, h₁₄.get .x5]⟩)) fun w' ⟨⟨k', m', e2, e5⟩, hv⟩ => ?_
  have g₁₃ : w₁₃.gpr = w₂.gpr := by rw [h₁₃.gpr, h₁₂.gpr, g₁₁]
  have c5 : (w₁₃.gpr .x5).toNat = 32 - c := by rw [g₁₃, k₂.get .x5, h.x5]
  have x5' : (w'.gpr .x5).toNat = 32 - (c + 1) := by
    rw [e5, toNat_sub_n (by rw [c5]; simp; omega), c5]; simp; omega
  refine ⟨⟨st₁₃.keep k' m' hv, ?_, ?_, x5', ?_⟩, by rw [x5']; omega⟩
  · rw [e2, g₁₃, k₂.get .x2, h.x2, coeffAddr, ptr_add, show 4 * (8 * c) + 32 = 4 * (8 * (c + 1)) by omega]
  · rw [k'.get .x12, g₁₃, e12, h.x12, ptr_add, show 4 * (64 + 2 * c) + 8 = 4 * (64 + 2 * (c + 1)) by omega]
  · -- the lanes stored
    set P' := nttLayerN R 2 (2 * c)
    have z0 : 64 + 2 * c < 128 := by omega
    rw [m', m₁₃, mw]
    refine polyIs_write16x2 h.poly hj hj' (by omega)
      (a := fun e => if e < 2 then P'[8 * c + e]! + zeta (64 + 2 * c) * P'[8 * c + e + 2]!
        else P'[8 * c + e - 2]! - zeta (64 + 2 * c) * P'[8 * c + e]!)
      (b := fun e => if e < 2 then P'[8 * c + 4 + e]! + zeta (64 + 2 * c + 1) * P'[8 * c + 4 + e + 2]!
        else P'[8 * c + 4 + e - 2]! - zeta (64 + 2 * c + 1) * P'[8 * c + 4 + e]!)
      (fun e he => ?_) (fun e he => ?_) fun i hi => ?_
    · rw [h₁₁.get .v5, h₁₀.v, vword_trn1_d2 _ _ he]
      rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp only [show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide, show ¬ (2 : Nat) < 2 by decide,
          show ¬ (3 : Nat) < 2 by decide, ite_true, ite_false]
      · rw [l2 0 (by decide), val_add', val_mul, Nat.mul_comm (zeta _).val]; rfl
      · rw [l2 1 (by decide), val_add', val_mul, Nat.mul_comm (zeta _).val]; rfl
      · rw [l1 0 (by decide), val_sub', val_mul, Nat.mul_comm (zeta _).val]; rfl
      · rw [l1 1 (by decide), val_sub', val_mul, Nat.mul_comm (zeta _).val]; rfl
    · rw [h₁₁.v, h₁₀.get .v2, h₁₀.get .v1, vword_trn2_d2 _ _ he]
      rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp only [show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide, show ¬ (2 : Nat) < 2 by decide,
          show ¬ (3 : Nat) < 2 by decide, ite_true, ite_false]
      · rw [l2 2 (by decide), val_add', val_mul, Nat.mul_comm (zeta _).val]
      · rw [l2 3 (by decide), val_add', val_mul, Nat.mul_comm (zeta _).val]
      · rw [l1 2 (by decide), val_sub', val_mul, Nat.mul_comm (zeta _).val]; rfl
      · rw [l1 3 (by decide), val_sub', val_mul, Nat.mul_comm (zeta _).val]; rfl
    · exact pair_poly R hc i hi

theorem last_ok {s₀ : State} (hp : Pre s₀) {u : State} (h : OInv s₀ 6 u) :
    WP isa nttLast u fun s' => St s₀ s' ∧
      PolyIs s'.mem (fP s₀) (nttLayer ((nttLens.take 6).foldl nttLayer (P₀ s₀)) 2) := by
  refine WP.seq ?_
  rw [← List.append_nil [mov .x2 .x0, Instr.movz .x .x5 32 0]]
  refine wp_scalar (by decide) (P := fun u₂ => Keep [.x2, .x5] u u₂ ∧ u₂.mem = u.mem ∧
      u₂.gpr .x2 = u.gpr .x0 ∧ (u₂.gpr .x5).toNat = 32)
    (wp_mov fun u₁ h₁ e₁ => wp_movz fun u₂ h₂ e₂ => wp_nil ⟨(h₁.keep.trans h₂.keep).mono,
      by rw [h₂.mem, h₁.mem], by rw [h₂.get .x2, e₁], by rw [e₂]; rfl⟩)
    fun u₂ ⟨k₂, m₂, e2, e5⟩ hv₂ => wp_nil ?_
  have i₀ : PInv s₀ ((nttLens.take 6).foldl nttLayer (P₀ s₀)) 0 u₂ :=
    ⟨h.st.keep k₂ m₂ hv₂, by rw [e2, h.st.x0, coeffAddr]; exact (BitVec.add_zero _).symm,
      by rw [k₂.get .x12, h.x12], by rw [e5], by rw [m₂, Nat.mul_zero, nttLayerN_zero]; exact h.poly⟩
  exact WP.mono (count_loop (by decide) (PInv s₀ _) (fun c hc w hw => pair_step hp hc hw) i₀)
    fun s' h' => ⟨h'.st, h'.poly⟩

/-- The registers of the layers' loops. -/
theorem setup_ok (s : State) :
    WP isa (.block [.movz .x .x11 32 0, .addImm .x .x12 .x1 4, .movz .x .x13 1 0, .movz .x .x14 6 0]) s
      fun s₆ => Keep [.x11, .x12, .x13, .x14] s s₆ ∧ s₆.mem = s.mem ∧
        (s₆.gpr .x11).toNat = 32 ∧ s₆.gpr .x12 = s.gpr .x1 + BitVec.ofNat 64 4 ∧
        (s₆.gpr .x13).toNat = 1 ∧ (s₆.gpr .x14).toNat = 6 :=
  wp_movz fun s₃ h₃ e₃ => wp_addImm (by decide) fun s₄ h₄ e₄ => wp_movz fun s₅ h₅ e₅ =>
    wp_movz fun s₆ h₆ e₆ => wp_nil ⟨(((h₃.keep.trans h₄.keep).trans h₅.keep).trans h₆.keep).mono,
      by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem], by rw [h₆.get .x11, h₅.get .x11, h₄.get .x11, e₃]; rfl,
      by rw [h₆.get .x12, h₅.get .x12, e₄, h₃.get .x1], by rw [h₆.get .x13, e₅]; rfl,
      by rw [e₆]; rfl⟩

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
  refine WP.mono (vconsts_ok s₁) fun s₂ ⟨k₂, m₂, vc₂, _⟩ => ?_
  refine WP.mono (WP.keepV (by decide) (setup_ok s₂)) fun s₆ ⟨⟨k₆, m₆, e11, e12, e13, e14⟩, hv₆⟩ => ?_
  have k₆' := ((h₁.keep.trans k₂).trans k₆)
  have fr : ∀ r ∈ [(⟨s₀.gpr .x1, 512⟩ : Region)], (polyRegion (fP s₀)).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.disj.sub_right (Region.sub_prefix (by decide))
  have i₀ : OInv s₀ 0 s₆ := by
    refine ⟨⟨k₆'.rd, k₆'.wr, k₆'.sp, k₆'.get .x0, ?_, fun k hk => by rw [m₆, m₂]; exact h₁.tab k hk⟩,
      by rw [e11], ?_, by rw [e13], by rw [e14], ?_⟩
    · exact ⟨by rw [hv₆]; exact vc₂.q, by rw [hv₆]; exact vc₂.m⟩
    · rw [e12, k₂.get .x1, h₁.keep.get .x1]
    · rw [m₆, m₂]
      exact polyIs_frame h₁.frame fr ⟨hp.red, rfl⟩
  refine WP.seq (WP.mono (count_loop (by decide) (OInv s₀) (fun i hi u h => layer_step hp hi h) i₀)
    fun u h => WP.mono (last_ok hp h) fun s' ⟨st, hpoly⟩ => ⟨st.sp, ?_⟩)
  show PolyIs s'.mem (fP s₀) (ntt (P₀ s₀))
  rw [ntt_eq_layers, ntt_eq_last]
  exact hpoly

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
