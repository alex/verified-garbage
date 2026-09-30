import VerifiedGarbage.Proof.MlKem.AArch64.NttFwd
import Mathlib.Tactic.Set

/-!
# ML-KEM on AArch64: `vg_mlkem_inv_ntt`

Untrusted: everything here is checked by Lean. As for the NTT
(`NttFwd.lean`), with the inverse butterflies and the zetas from
`zetas[127]` down: the layer with `len = 2` two blocks at a time
(`ipair_step`), the layers with `len ≥ 4` (`ivstep`, `iblock_step`,
`ilayer_step`), then the multiplication by 3303 (`scale_step`).
-/

namespace VG.Proof.MlKem.AArch64.Ntt

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem

theorem ptr_prev (p : Addr) {k : Nat} (hk : 1 ≤ k) :
    p + BitVec.ofNat 64 (4 * k) - BitVec.ofNat 64 4 = p + BitVec.ofNat 64 (4 * (k - 1)) := by
  rw [show 4 * k = 4 * (k - 1) + 4 by omega, ← ptr_add, BitVec.add_sub_cancel]

theorem ptr_prev2 (p : Addr) {k : Nat} (hk : 2 ≤ k) :
    p + BitVec.ofNat 64 (4 * k) - BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (4 * (k - 2)) := by
  rw [show 4 * k = 4 * (k - 2) + 8 by omega, ← ptr_add, BitVec.add_sub_cancel]

/-! ## The layer with `len = 2` -/

/-- The zetas `k` and `k + 1` loaded as a pair, swapped, and spread over the
lanes as `(ζ_{k+1}, ζ_{k+1}, ζ_k, ζ_k)`. -/
theorem lanes_zpair_rev {s₀ s : State} (h : St s₀ s) {k : Nat} (hk : k + 1 < 128) :
    Lanes (VPermOp.eval .zip1 .s4
      (VRevOp.eval .rev64s (ofVDwords (s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 64)
        (s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 64)))
      (VRevOp.eval .rev64s (ofVDwords (s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 64)
        (s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 64))))
      fun e => (zeta (k + 1 - e / 2)).val := fun e he => by
  show _ = (zeta (k + 1 - e / 2)).val
  rw [vword_zip1_s4 _ he, vword_rev64s _ (by omega)]
  have t : ∀ j, j < 128 → ((s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * j)) 32)).toNat = (zeta j).val :=
    fun j hj => by
      rw [h.tab j hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
          have := zetaTable_lt j hj; have hq : q = 3329 := rfl; omega),
        zetaTable_zeta hj]
  rcases (show e / 2 = 0 ∨ e / 2 = 1 by omega) with e2 | e2 <;> rw [e2]
  · rw [vword_dup_d2 _ (by decide), show 32 * ((if 0 % 2 = 0 then 0 + 1 else 0 - 1) % 2) = 32 from rfl,
      readW64_hi, ptr_add,
      show 4 * k + 4 = 4 * (k + 1) by omega, show k + 1 - 0 = k + 1 from rfl]
    exact t (k + 1) hk
  · rw [vword_dup_d2 _ (by decide), show 32 * ((if 1 % 2 = 0 then 1 + 1 else 1 - 1) % 2) = 0 from rfl,
      readW64_lo, show k + 1 - 1 = k by omega]
    exact t k (by omega)

/-- After `c` pairs of the blocks of the layer with `len = 2`. -/
structure PInvI (s₀ : State) (R : Poly) (c : Nat) (w : State) : Prop where
  st : St s₀ w
  x2 : w.gpr .x2 = coeffAddr (fP s₀) (8 * c)
  x12 : w.gpr .x12 = sP s₀ + BitVec.ofNat 64 (4 * (126 - 2 * c))
  x5 : (w.gpr .x5).toNat = 32 - c
  poly : PolyIs w.mem (fP s₀) (nttInvLayerN R 2 (2 * c))

theorem ipair_step {s₀ : State} (hp : Pre s₀) {R : Poly} {c : Nat} (hc : c < 32) {w : State}
    (h : PInvI s₀ R c w) :
    WP isa (.block (vPairBody (vibfly .v18) true [.subImm .x .x12 .x12 8])) w fun w' =>
      PInvI s₀ R (c + 1) w' ∧ ((w'.gpr .x5).toNat ≠ 0 ↔ c + 1 ≠ 32) := by
  show WP isa (.block ([.ldr .x .x17 .x12 0, .subImm .x .x12 .x12 8] ++
    (.vop (.dup .d2 .v19 .x17) :: .vop (.rev .rev64s .v19 .v19) :: .vop (.perm .zip1 .s4 .v18 .v19 .v19) ::
      .ldrq .v5 .x2 0 :: .ldrq .v6 .x2 16 :: .vop (.perm .trn1 .d2 .v0 .v5 .v6) ::
      .vop (.perm .trn2 .d2 .v1 .v5 .v6) ::
      (vibfly .v18 ++ (.vop (.perm .trn1 .d2 .v5 .v2 .v1) :: .vop (.perm .trn2 .d2 .v6 .v2 .v1) ::
        .strq .v5 .x2 0 :: .strq .v6 .x2 16 ::
        ([.addImm .x .x2 .x2 32, .subImm .x .x5 .x5 1] ++ [])))))) w _
  have hk : 4 * (126 - 2 * c) + 8 ≤ 1024 := by omega
  refine wp_scalar (by decide) (P := fun w₂ => Keep [.x17, .x12] w w₂ ∧ w₂.mem = w.mem ∧
      w₂.gpr .x17 = w.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * (126 - 2 * c))) 64 ∧
      w₂.gpr .x12 = w.gpr .x12 - BitVec.ofNat 64 8)
    (wp_ldrx (a := sP s₀ + BitVec.ofNat 64 (4 * (126 - 2 * c))) (by decide) (by rw [h.x12, ptr_zero])
      (by rw [h.st.rd, h.st.wr, hp.rd, hp.wr]
          exact in_regions (R := polyRegion (sP s₀)) (by simp) (contains_off hk (by decide)))
      fun w₁ h₁ e₁ => wp_subImm (by decide) fun w₂ h₂ e₂ =>
        wp_nil ⟨(h₁.keep.trans h₂.keep).mono, by rw [h₂.mem, h₁.mem], by rw [h₂.get .x17, e₁],
          by rw [e₂, h₁.get .x12]⟩) fun w₂ ⟨k₂, m₂, e17, e12⟩ hv₂ => ?_
  have st₂ := h.st.keep k₂ m₂ hv₂
  refine wp_vop (d := .v19) rfl fun w₃ h₃ => wp_vop (d := .v19) rfl fun w₃' h₃' =>
    wp_vop (d := .v18) rfl fun w₄ h₄ => ?_
  have lz : Lanes (w₄.v .v18) fun e => (zeta (126 - 2 * c + 1 - e / 2)).val := by
    rw [h₄.v, h₃'.v, h₃.v, e17, ← m₂]; exact lanes_zpair_rev st₂ (by omega)
  have hj : 8 * c + 4 ≤ 256 := by omega
  have hj' : 8 * c + 4 + 4 ≤ 256 := by omega
  have g₄ : w₄.gpr = w₂.gpr := by rw [h₄.gpr, h₃'.gpr, h₃.gpr]
  have mw₄ : w₄.mem = w.mem := by rw [h₄.mem, h₃'.mem, h₃.mem, m₂]
  have st₄ := st₂.vchg ((h₃.chg.trans h₃'.chg).trans h₄.chg)
  refine wp_ldrq (a := coeffAddr (fP s₀) (8 * c)) (by decide) (by rw [g₄, k₂.get .x2, h.x2, ptr_zero])
    (hp.in16' st₄ hj) fun w₅ h₅ => ?_
  refine wp_ldrq (a := coeffAddr (fP s₀) (8 * c + 4)) (by decide)
    (by rw [h₅.gpr, g₄, k₂.get .x2, h.x2, coeffAddr_step])
    (by rw [h₅.rd, h₅.wr]; exact hp.in16' st₄ hj') fun w₆ h₆ => ?_
  have l5 : Lanes (w₆.v .v5) fun e => ((nttInvLayerN R 2 (2 * c))[8 * c + e]!).val := by
    rw [h₆.get .v5, h₅.v, mw₄]; exact lanes_load h.poly hj
  have l6 : Lanes (w₆.v .v6) fun e => ((nttInvLayerN R 2 (2 * c))[8 * c + 4 + e]!).val := by
    rw [h₆.v, h₅.mem, mw₄]; exact lanes_load h.poly hj'
  refine wp_vop (d := .v0) rfl fun w₇ h₇ => wp_vop (d := .v1) rfl fun w₈ h₈ => ?_
  have lA : Lanes (w₈.v .v0) fun e => ((nttInvLayerN R 2 (2 * c))[8 * c + e + 2 * (e / 2)]!).val :=
    fun e he => by
      show _ = ((nttInvLayerN R 2 (2 * c))[8 * c + e + 2 * (e / 2)]!).val
      rw [h₈.get .v0, h₇.v, vword_trn1_d2 _ _ he]
      rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl
      · exact l5 0 (by decide)
      · exact l5 1 (by decide)
      · exact l6 0 (by decide)
      · exact l6 1 (by decide)
  have lB : Lanes (w₈.v .v1) fun e =>
      ((nttInvLayerN R 2 (2 * c))[8 * c + e + 2 * (e / 2) + 2]!).val :=
    fun e he => by
      show _ = ((nttInvLayerN R 2 (2 * c))[8 * c + e + 2 * (e / 2) + 2]!).val
      rw [h₈.v, h₇.get .v5, h₇.get .v6, vword_trn2_d2 _ _ he]
      rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl
      · exact l5 2 (by decide)
      · exact l5 3 (by decide)
      · exact l6 2 (by decide)
      · exact l6 3 (by decide)
  have lZ : Lanes (w₈.v .v18) fun e => (zeta (126 - 2 * c + 1 - e / 2)).val := by
    rw [h₈.get .v18, h₇.get .v18, h₆.get .v18, h₅.get .v18]; exact lz
  have st₈ := st₄.vchg (((h₅.chg.trans h₆.chg).trans h₇.chg).trans h₈.chg)
  refine vibfly_ok (hc := st₈.vc) (hA := lA) (hA' := fun _ _ => val_lt _) (hB := lB)
    (hB' := fun _ _ => val_lt _) (hZ := lZ) (hZ' := fun _ _ => val_lt _) (k := fun w₉ h₉ l2 l1 => ?_)
  refine wp_vop (d := .v5) rfl fun w₁₀ h₁₀ => wp_vop (d := .v6) rfl fun w₁₁ h₁₁ => ?_
  have st₁₁ := st₈.vchg ((h₉.trans h₁₀.chg).trans h₁₁.chg)
  have g₁₁ : w₁₁.gpr = w₂.gpr := by
    rw [h₁₁.gpr, h₁₀.gpr, h₉.gpr, h₈.gpr, h₇.gpr, h₆.gpr, h₅.gpr, g₄]
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
  · rw [k'.get .x12, g₁₃, e12, h.x12, ptr_prev2 _ (by omega), show 126 - 2 * c - 2 = 126 - 2 * (c + 1) by omega]
  · set P' := nttInvLayerN R 2 (2 * c)
    rw [m', m₁₃, mw]
    refine polyIs_write16x2 h.poly hj hj' (by omega)
      (a := fun e => if e < 2 then P'[8 * c + e]! + P'[8 * c + e + 2]!
        else zeta (127 - 2 * c) * (P'[8 * c + e]! - P'[8 * c + e - 2]!))
      (b := fun e => if e < 2 then P'[8 * c + 4 + e]! + P'[8 * c + 4 + e + 2]!
        else zeta (126 - 2 * c) * (P'[8 * c + 4 + e]! - P'[8 * c + 4 + e - 2]!))
      (fun e he => ?_) (fun e he => ?_) fun i hi => ?_
    · rw [h₁₁.get .v5, h₁₀.v, vword_trn1_d2 _ _ he]
      rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp only [show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide, show ¬ (2 : Nat) < 2 by decide,
          show ¬ (3 : Nat) < 2 by decide, ite_true, ite_false]
      · rw [l2 0 (by decide), val_add']
      · rw [l2 1 (by decide), val_add']
      · rw [l1 0 (by decide), val_mul, val_sub', Nat.mul_comm (zeta _).val]
        dsimp only
        rw [show 126 - 2 * c + 1 - 0 / 2 = 127 - 2 * c by omega]; rfl
      · rw [l1 1 (by decide), val_mul, val_sub', Nat.mul_comm (zeta _).val]
        dsimp only
        rw [show 126 - 2 * c + 1 - 1 / 2 = 127 - 2 * c by omega]; rfl
    · rw [h₁₁.v, h₁₀.get .v2, h₁₀.get .v1, vword_trn2_d2 _ _ he]
      rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
        simp only [show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide, show ¬ (2 : Nat) < 2 by decide,
          show ¬ (3 : Nat) < 2 by decide, ite_true, ite_false]
      · rw [l2 2 (by decide), val_add']
      · rw [l2 3 (by decide), val_add']
      · rw [l1 2 (by decide), val_mul, val_sub', Nat.mul_comm (zeta _).val]
        dsimp only
        rw [show 126 - 2 * c + 1 - 2 / 2 = 126 - 2 * c by omega]; rfl
      · rw [l1 3 (by decide), val_mul, val_sub', Nat.mul_comm (zeta _).val]
        dsimp only
        rw [show 126 - 2 * c + 1 - 3 / 2 = 126 - 2 * c by omega]; rfl
    · have hn : i < n := by rw [n_eq]; exact hi
      rw [show 2 * (c + 1) = 2 * c + 1 + 1 by omega, nttInvLayerN_succ, nttInvLayerN_succ,
        nttInvBlock_get _ (by decide) (by rw [n_eq]; omega) hn,
        show 256 / 2 - 1 - (2 * c + 1) = 126 - 2 * c by omega,
        show 2 * 2 * (2 * c + 1) = 8 * c + 4 by omega]
      have Qg : ∀ x < 256, (nttInvBlock P' 2 (256 / 2 - 1 - 2 * c) (2 * 2 * (2 * c)))[x]! =
          if 8 * c ≤ x ∧ x < 8 * c + 2 then P'[x]! + P'[x + 2]!
          else if 8 * c + 2 ≤ x ∧ x < 8 * c + 4 then zeta (127 - 2 * c) * (P'[x]! - P'[x - 2]!)
          else P'[x]! := fun x hx => by
        rw [nttInvBlock_get _ (by decide) (by rw [n_eq]; omega) (by rw [n_eq]; exact hx),
          show 256 / 2 - 1 - 2 * c = 127 - 2 * c by omega, show 2 * 2 * (2 * c) = 8 * c by omega]
      rcases (by omega : i < 8 * c ∨ (8 * c ≤ i ∧ i < 8 * c + 2) ∨ (8 * c + 2 ≤ i ∧ i < 8 * c + 4) ∨
          (8 * c + 4 ≤ i ∧ i < 8 * c + 6) ∨ (8 * c + 6 ≤ i ∧ i < 8 * c + 8) ∨ 8 * c + 8 ≤ i) with
        h | h | h | h | h | h
      · rw [Qg i hi]
        simp (disch := omega) only [ite_eq_left, ite_eq_right]
        rfl
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
        rfl

/-! ## The layers with `len ≥ 4` -/

/-- After `u` vectors of four butterflies of the block from `start`. -/
structure IInvI (s₀ : State) (P : Poly) (len k start : Nat) (s : State) (u : Nat) (w : State) : Prop where
  st : St s₀ w
  keep : Keep [.x2, .x3, .x5] s w
  z : Lanes (w.v .v18) fun _ => (zeta k).val
  x2 : w.gpr .x2 = coeffAddr (fP s₀) (start + 4 * u)
  x3 : w.gpr .x3 = coeffAddr (fP s₀) (start + len + 4 * u)
  x5 : (w.gpr .x5).toNat = len / 4 - u
  poly : PolyIs w.mem (fP s₀) (nttInvBlockN P len k start (4 * u))

theorem ivstep {s₀ : State} (hp : Pre s₀) {P : Poly} {len k start : Nat} (hs : start + 2 * len ≤ 256)
    {s : State} {u : Nat} (hu : 4 * u + 4 ≤ len) {w : State} (h : IInvI s₀ P len k start s u w) :
    WP isa (.block (vBody (vibfly .v18))) w fun w' => IInvI s₀ P len k start s (u + 1) w' ∧
      ((w'.gpr .x5).toNat ≠ 0 ↔ u + 1 ≠ len / 4) := by
  have hj : start + 4 * u + 4 ≤ 256 := by omega
  have hj' : start + len + 4 * u + 4 ≤ 256 := by omega
  simp only [vBody, List.cons_append, List.nil_append]
  refine wp_ldrq (a := coeffAddr (fP s₀) (start + 4 * u)) (by decide) (by rw [h.x2, ptr_zero])
    (hp.in16' h.st hj) fun w₁ h₁ => ?_
  refine wp_ldrq (a := coeffAddr (fP s₀) (start + len + 4 * u)) (by decide) (by rw [h₁.gpr, h.x3, ptr_zero])
    (by rw [h₁.rd, h₁.wr]; exact hp.in16' h.st hj') fun w₂ h₂ => ?_
  have la : Lanes (w₂.v .v0) fun e => ((nttInvBlockN P len k start (4 * u))[start + 4 * u + e]!).val := by
    rw [h₂.get .v0, h₁.v]; exact lanes_load h.poly hj
  have lb : Lanes (w₂.v .v1) fun e =>
      ((nttInvBlockN P len k start (4 * u))[start + len + 4 * u + e]!).val := by
    rw [h₂.v, h₁.mem]; exact lanes_load h.poly hj'
  have lz : Lanes (w₂.v .v18) fun _ => (zeta k).val := by rw [h₂.get .v18, h₁.get .v18]; exact h.z
  have st₂ := h.st.vchg (h₁.chg.trans h₂.chg)
  refine vibfly_ok (hc := st₂.vc) (hA := la) (hA' := fun _ _ => val_lt _) (hB := lb)
    (hB' := fun _ _ => val_lt _) (hZ := lz) (hZ' := fun _ _ => val_lt _) (k := fun w₃ h₃ l2 l1 => ?_)
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
      (a := fun e => (nttInvBlockN P len k start (4 * u))[start + 4 * u + e]! +
        (nttInvBlockN P len k start (4 * u))[start + len + 4 * u + e]!)
      (b := fun e => zeta k * ((nttInvBlockN P len k start (4 * u))[start + len + 4 * u + e]! -
        (nttInvBlockN P len k start (4 * u))[start + 4 * u + e]!))
      (l2.congr fun e he => ?_) (l1.congr fun e he => ?_) fun i hi => ?_
    · rw [val_add']
    · rw [val_mul, val_sub', Nat.mul_comm (zeta k).val]
    · rw [show 4 * (u + 1) = 4 * u + 4 by omega, nttInvBlockN_add,
        nttInvBlockN_get' _ (by omega) (by omega) (by rw [n_eq]; omega) (by rw [n_eq]; exact hi)]
      by_cases c1 : start + 4 * u ≤ i ∧ i < start + 4 * u + 4
      · rw [ite_eq_left c1, ite_eq_left c1, show start + 4 * u + (i - (start + 4 * u)) = i by omega,
          show start + len + 4 * u + (i - (start + 4 * u)) = i + len by omega]
      · rw [ite_eq_right c1, ite_eq_right c1]
        by_cases c2 : start + 4 * u + len ≤ i ∧ i < start + 4 * u + len + 4
        · rw [ite_eq_left c2, ite_eq_left (by omega),
            show start + 4 * u + (i - (start + len + 4 * u)) = i - len by omega,
            show start + len + 4 * u + (i - (start + len + 4 * u)) = i by omega]
        · rw [ite_eq_right c2, ite_eq_right (by omega)]

/-- After `b` blocks of the layer with `len`. -/
structure LInvI (s₀ : State) (P : Poly) (len : Nat) (L : State) (b : Nat) (u : State) : Prop where
  st : St s₀ u
  keep : Keep kRegs L u
  x2 : u.gpr .x2 = fP s₀ + BitVec.ofNat 64 (4 * (2 * len * b))
  x12 : u.gpr .x12 = sP s₀ + BitVec.ofNat 64 (4 * (256 / len - 1 - b))
  x16 : (u.gpr .x16).toNat = 128 / len - b
  poly : PolyIs u.mem (fP s₀) (nttInvLayerN P len b)

/-- One block. -/
theorem iblock_step {s₀ : State} (hp : Pre s₀) {P : Poly} {len : Nat} (h4 : 4 ≤ len) (hl4 : len % 4 = 0)
    (hnb : len * (128 / len) = 128) (hk : 2 * (128 / len) ≤ 128) (h256 : 256 / len = 2 * (128 / len))
    {L : State}
    (h11 : (L.gpr .x11).toNat = len / 4) (h15 : (L.gpr .x15).toNat = len * 4) {b : Nat}
    (hb : b < 128 / len) {u : State} (h : LInvI s₀ P len L b u) :
    WP isa (vBlockCode (vibfly .v18) [.subImm .x .x12 .x12 4]) u fun u' => LInvI s₀ P len L (b + 1) u' ∧
      ((u'.gpr .x16).toNat ≠ 0 ↔ b + 1 ≠ 128 / len) := by
  have hbl : 2 * len * b + 2 * len ≤ 256 := by
    have : len * (b + 1) ≤ len * (128 / len) := Nat.mul_le_mul_left _ hb
    rw [Nat.mul_succ] at this
    rw [Nat.mul_assoc]
    omega
  have hk' : 256 / len - 1 - b < 128 := by omega
  have hk1 : 1 ≤ 256 / len - 1 - b := by omega
  refine WP.seq ?_
  show WP isa (.block ([Instr.ldr .w .x17 .x12 0, .subImm .x .x12 .x12 4] ++
    (.vop (.dup .s4 .v18 .x17) :: ([.add .x .x3 .x2 .x15, mov .x5 .x11] ++ [])))) u _
  refine wp_scalar (by decide) (P := fun u₂ => Keep [.x17, .x12] u u₂ ∧ u₂.mem = u.mem ∧
      u₂.gpr .x17 = (u.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * (256 / len - 1 - b))) 32).setWidth 64 ∧
      u₂.gpr .x12 = u.gpr .x12 - BitVec.ofNat 64 4)
    (wp_ldrw (a := sP s₀ + BitVec.ofNat 64 (4 * (256 / len - 1 - b))) (by decide) (by rw [h.x12, ptr_zero])
      (hp.in_tab h.st hk') fun u₁ h₁ e₁ => wp_subImm (by decide) fun u₂ h₂ e₂ =>
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
  have z₄ : Lanes (u₄.v .v18) fun _ => (zeta (256 / len - 1 - b)).val := by
    rw [hv₄, h₃.v, e17, ← m₂]; exact lanes_zeta st₂ hk'
  have i₀ : IInvI s₀ (nttInvLayerN P len b) len (256 / len - 1 - b) (2 * len * b) u₄ 0 u₄ := by
    refine ⟨st₄, Keep.refl _ _, z₄, ?_, ?_, ?_, ?_⟩
    · rw [k₄.get .x2, g₃, k₂.get .x2, h.x2, coeffAddr, Nat.mul_zero, Nat.add_zero]
    · have e15 : u₃.gpr .x15 = BitVec.ofNat 64 (len * 4) := by
        apply BitVec.eq_of_toNat_eq
        rw [g₃, k₂.get .x15, h.keep.get .x15, h15, toNat_ofNat_lt (by omega)]
      rw [e3, g₃, k₂.get .x2, h.x2, ← g₃, e15, ptr_add, coeffAddr, Nat.mul_zero, Nat.add_zero]
      congr 2; rw [Nat.mul_comm len 4, Nat.mul_add]
    · rw [e5, g₃, k₂.get .x11, h.keep.get .x11, h11, Nat.sub_zero]
    · rw [m₄, h₃.mem, m₂, nttInvBlockN_zero]; exact h.poly
  refine WP.seq (WP.mono (count_loop (n := len / 4) (by omega) (IInvI s₀ (nttInvLayerN P len b) len
    (256 / len - 1 - b) (2 * len * b) u₄) (fun t ht w hw => ivstep hp hbl (by omega) hw) i₀) fun u₅ h₅ => ?_)
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
  · rw [k₇.get .x12, h₅.keep.get .x12, k₄.get .x12, g₃, e12, h.x12, ptr_prev _ (by omega),
      show 256 / len - 1 - b - 1 = 256 / len - 1 - (b + 1) by omega]
  · have p₅ := h₅.poly
    rw [show 4 * (len / 4) = len by omega] at p₅
    rw [m₇, nttInvLayerN_succ, nttInvBlock]
    exact p₅

/-- The layers with `len ≥ 4`: `len = 4 · 2ⁱ`, `32 / 2ⁱ` blocks. -/
theorem ifacts : ∀ i < 6, 4 ≤ 4 * 2 ^ i ∧ 4 * 2 ^ i % 4 = 0 ∧ 128 / (4 * 2 ^ i) = 32 / 2 ^ i ∧
    4 * 2 ^ i * (128 / (4 * 2 ^ i)) = 128 ∧ 2 * (128 / (4 * 2 ^ i)) ≤ 128 ∧
    256 / (4 * 2 ^ i) = 2 * (128 / (4 * 2 ^ i)) ∧ 4 * 2 ^ i / 4 = 2 ^ i ∧
    256 / (4 * 2 ^ i) - 1 - 128 / (4 * 2 ^ i) = 64 / 2 ^ (i + 1) - 1 ∧ 256 / (4 * 2 ^ i) = 64 / 2 ^ i ∧
    32 / 2 ^ i / 2 = 32 / 2 ^ (i + 1) ∧ nttInvLens.getD (i + 1) 0 = 4 * 2 ^ i ∧ 0 < 32 / 2 ^ i ∧
    2 ^ i ≤ 32 := by
  decide

/-- After the layer with `len = 2` and `i` more. -/
structure OInvI (s₀ : State) (i : Nat) (u : State) : Prop where
  st : St s₀ u
  x11 : (u.gpr .x11).toNat = 2 ^ i
  x12 : u.gpr .x12 = sP s₀ + BitVec.ofNat 64 (4 * (64 / 2 ^ i - 1))
  x13 : (u.gpr .x13).toNat = 32 / 2 ^ i
  x14 : (u.gpr .x14).toNat = 6 - i
  poly : PolyIs u.mem (fP s₀) ((nttInvLens.take (i + 1)).foldl nttInvLayer (P₀ s₀))

/-- One layer with `len ≥ 4`. -/
theorem ilayer_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 6) {u : State} (h : OInvI s₀ i u) :
    WP isa nttInvLayerCode u fun u' => OInvI s₀ (i + 1) u' ∧ ((u'.gpr .x14).toNat ≠ 0 ↔ i + 1 ≠ 6) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := ifacts i hi
  refine WP.seq ?_
  show WP isa (.block ([mov .x2 .x0, mov .x16 .x13, .lsl .x .x15 .x11 4] ++ [])) u _
  refine wp_scalar (by decide) (P := fun u₃ => Keep [.x2, .x16, .x15] u u₃ ∧ u₃.mem = u.mem ∧
      u₃.gpr .x2 = u.gpr .x0 ∧ u₃.gpr .x16 = u.gpr .x13 ∧ u₃.gpr .x15 = u.gpr .x11 <<< 4)
    (wp_mov fun u₁ h₁ e₁ => wp_mov fun u₂ h₂ e₂ => wp_lsl (by decide) fun u₃ h₃ e₃ =>
      wp_nil ⟨((h₁.keep.trans h₂.keep).trans h₃.keep).mono, by rw [h₃.mem, h₂.mem, h₁.mem],
        by rw [h₃.get .x2, h₂.get .x2, e₁], by rw [h₃.get .x16, e₂, h₁.get .x13],
        by rw [e₃, h₂.get .x11, h₁.get .x11]⟩) fun u₃ ⟨k₃, m₃, e2, e16, e15⟩ hv₃ => wp_nil ?_
  have c11 : (u₃.gpr .x11).toNat = 4 * 2 ^ i / 4 := by rw [k₃.get .x11, h.x11, f6]
  have c15 : (u₃.gpr .x15).toNat = 4 * 2 ^ i * 4 := by
    rw [e15, toNat_lsl_n (by rw [h.x11]; omega), h.x11]; omega
  have l₀ : LInvI s₀ ((nttInvLens.take (i + 1)).foldl nttInvLayer (P₀ s₀)) (4 * 2 ^ i) u₃ 0 u₃ := by
    refine ⟨h.st.keep k₃ m₃ hv₃, Keep.refl _ _, ?_, ?_, ?_, by rw [m₃, nttInvLayerN_zero]; exact h.poly⟩
    · rw [e2, h.st.x0, Nat.mul_zero, Nat.mul_zero, ptr_zero]
    · rw [k₃.get .x12, h.x12, f8, Nat.sub_zero]
    · rw [e16, h.x13, f2, Nat.sub_zero]
  refine WP.seq (WP.mono (count_loop (n := 128 / (4 * 2 ^ i)) (by rw [f2]; exact f11)
    (LInvI s₀ _ (4 * 2 ^ i) u₃) (fun b hb v hv => iblock_step hp f0 f1 f3 f4 f5 c11 c15 hb hv) l₀)
    fun u₄ h₄ => ?_)
  show WP isa (.block ([.lsl .x .x11 .x11 1, .lsr .x .x13 .x13 1, .subImm .x .x14 .x14 1] ++ [])) u₄ _
  refine wp_scalar (by decide) (P := fun u₇ => Keep [.x11, .x13, .x14] u₄ u₇ ∧ u₇.mem = u₄.mem ∧
      u₇.gpr .x11 = u₄.gpr .x11 <<< 1 ∧ u₇.gpr .x13 = u₄.gpr .x13 >>> 1 ∧
      u₇.gpr .x14 = u₄.gpr .x14 - BitVec.ofNat 64 1)
    (wp_lsl (by decide) fun u₅ h₅ e₅ => wp_lsr (by decide) fun u₆ h₆ e₆ => wp_subImm (by decide)
      fun u₇ h₇ e₇ => wp_nil ⟨((h₅.keep.trans h₆.keep).trans h₇.keep).mono, by rw [h₇.mem, h₆.mem, h₅.mem],
        by rw [h₇.get .x11, h₆.get .x11, e₅], by rw [h₇.get .x13, e₆, h₅.get .x13],
        by rw [e₇, h₆.get .x14, h₅.get .x14]⟩) fun u₇ ⟨k₇, m₇, e11, e13, e14⟩ hv₇ => wp_nil ?_
  have c14 : (u₄.gpr .x14).toNat = 6 - i := by rw [h₄.keep.get .x14, k₃.get .x14, h.x14]
  have v14 : (u₇.gpr .x14).toNat = 6 - (i + 1) := by
    rw [e14, toNat_sub_n (by rw [c14]; simp; omega), c14]
    simp
    omega
  have c11' : (u₄.gpr .x11).toNat = 2 ^ i := by rw [h₄.keep.get .x11, k₃.get .x11, h.x11]
  refine ⟨⟨h₄.st.keep k₇ m₇ hv₇, ?_, ?_, ?_, v14, ?_⟩, by rw [v14]; omega⟩
  · rw [e11, toNat_lsl_n (by rw [c11']; omega), c11', Nat.pow_succ 2 i, Nat.pow_one]
  · rw [k₇.get .x12, h₄.x12, f7]
  · rw [e13, toNat_lsr, h₄.keep.get .x13, k₃.get .x13, h.x13, ← f9]
  · rw [m₇, foldl_take_succ _ _ _ 0 (by rw [show nttInvLens.length = 7 from rfl]; omega), f10]
    exact h₄.poly

/-! ## The multiplication by 3303 -/

section
variable (R : Poly)

/-- Coefficient `i` after the scaling. -/
def SG (i : Nat) : BitVec 32 := BitVec.ofNat 32 (R[i]! * 3303).val
/-- Coefficient `i` before it. -/
def SO (i : Nat) : BitVec 32 := BitVec.ofNat 32 (R[i]!).val

end

theorem CoeffsUpTo.write16 {m : Mem} {p : Addr} {t : Nat} {G old : Nat → BitVec 32}
    (h : CoeffsUpTo m p t G old) (ht : t + 4 ≤ 256) {x : BitVec 128}
    (hx : ∀ e < 4, vword x e = G (t + e)) : CoeffsUpTo (m.write (coeffAddr p t) 16 x) p (t + 4) G old :=
  fun i hi => by
    rw [coeffAt_write16 _ _ ht _ hi, h i hi]
    by_cases c : t ≤ i ∧ i < t + 4
    · rw [ite_eq_left c, ite_eq_left (by omega), hx _ (by omega), show t + (i - t) = i by omega]
    · rw [ite_eq_right c]
      by_cases c' : i < t
      · rw [ite_eq_left c', ite_eq_left (by omega)]
      · rw [ite_eq_right c', ite_eq_right (by omega)]

/-- After `k` vectors scaled. -/
structure SInv (s₀ : State) (R : Poly) (k : Nat) (u : State) : Prop where
  st : St s₀ u
  z : Lanes (u.v .v18) fun _ => 3303
  x2 : u.gpr .x2 = coeffAddr (fP s₀) (4 * k)
  x5 : (u.gpr .x5).toNat = 64 - k
  out : CoeffsUpTo u.mem (fP s₀) (4 * k) (SG R) (SO R)

theorem scale_step {s₀ : State} (hp : Pre s₀) {R : Poly} {k : Nat} (hk : k < 64) {u : State}
    (h : SInv s₀ R k u) :
    WP isa (.block vScaleBody) u fun u' =>
      SInv s₀ R (k + 1) u' ∧ ((u'.gpr .x5).toNat ≠ 0 ↔ k + 1 ≠ 64) := by
  have hj : 4 * k + 4 ≤ 256 := by omega
  show WP isa (.block (.ldrq .v1 .x2 0 :: (vmulq .v1 .v18 .v3 ++ (.strq .v1 .x2 0 ::
    ([.addImm .x .x2 .x2 16, .subImm .x .x5 .x5 1] ++ []))))) u _
  refine wp_ldrq (a := coeffAddr (fP s₀) (4 * k)) (by decide) (by rw [h.x2, ptr_zero])
    (hp.in16' h.st hj) fun u₁ h₁ => ?_
  have l1 : Lanes (u₁.v .v1) fun e => (R[4 * k + e]!).val := fun e he => by
    show _ = (R[4 * k + e]!).val
    rw [h₁.v, read16, vword_ofVWords _ _ _ _ he]
    have c : ∀ j, j < 4 → (u.mem.readW (coeffAddr (fP s₀) (4 * k) + BitVec.ofNat 64 (4 * j)) 32).toNat =
        (R[4 * k + j]!).val := fun j hj' => by
      rw [coeffAddr_off, ← coeffAt_eq, h.out _ (by omega), ite_eq_right (by omega), SO,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt R[4 * k + j]!; omega)]
    rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl
    · exact c 0 (by decide)
    · exact c 1 (by decide)
    · exact c 2 (by decide)
    · exact c 3 (by decide)
  have st₁ := h.st.vchg h₁.chg
  refine vmulq_ok (d := .v1) (z := .v18) (t := .v3) (hc := st₁.vc) (hf := l1)
    (hf' := fun _ _ => val_lt _) (hg := by rw [h₁.get .v18]; exact h.z) (hg' := fun _ _ => by decide)
    (k := fun u₂ h₂ l₂ => ?_)
  have st₂ := st₁.vchg h₂
  refine wp_strq (a := coeffAddr (fP s₀) (4 * k)) (by decide)
    (by rw [h₂.gpr, h₁.gpr, h.x2, ptr_zero]) (hp.in16 st₂ hj) fun u₃ h₃ => ?_
  have st₃ : St s₀ u₃ := ⟨by rw [h₃.rd, st₂.rd], by rw [h₃.wr, st₂.wr], by rw [h₃.sp, st₂.sp],
    by rw [h₃.gpr, st₂.x0], ⟨by rw [h₃.v]; exact st₂.vc.q, by rw [h₃.v]; exact st₂.vc.m⟩,
    hp.tab_write (by rw [h₃.mem]; exact frame16 (Frame.refl _ _) hj _) st₂.tab⟩
  refine WP.mono (WP.keepV (Q := fun w' => Keep [.x2, .x5] u₃ w' ∧ w'.mem = u₃.mem ∧
      w'.gpr .x2 = u₃.gpr .x2 + BitVec.ofNat 64 16 ∧ w'.gpr .x5 = u₃.gpr .x5 - BitVec.ofNat 64 1)
      (by decide)
    (wp_addImm (by decide) fun u₄ h₄ e₄ => wp_subImm (by decide) fun u₅ h₅ e₅ =>
      wp_nil ⟨(h₄.keep.trans h₅.keep).mono, by rw [h₅.mem, h₄.mem], by rw [h₅.get .x2, e₄],
        by rw [e₅, h₄.get .x5]⟩)) fun w' ⟨⟨k', m', e2, e5⟩, hv⟩ => ?_
  have g₃ : u₃.gpr = u.gpr := by rw [h₃.gpr, h₂.gpr, h₁.gpr]
  have c5 : (u₃.gpr .x5).toNat = 64 - k := by rw [g₃, h.x5]
  have x5' : (w'.gpr .x5).toNat = 64 - (k + 1) := by
    rw [e5, toNat_sub_n (by rw [c5]; simp; omega), c5]; simp; omega
  refine ⟨⟨st₃.keep k' m' hv, ?_, ?_, x5', ?_⟩, by rw [x5']; omega⟩
  · rw [hv, h₃.v, h₂.get .v18, h₁.get .v18]; exact h.z
  · rw [e2, g₃, h.x2, coeffAddr_step, show 4 * k + 4 = 4 * (k + 1) by omega]
  · rw [m', h₃.mem, h₂.mem, h₁.mem, show 4 * (k + 1) = 4 * k + 4 by omega]
    refine CoeffsUpTo.write16 h.out hj fun e he => BitVec.eq_of_toNat_eq ?_
    rw [l₂ e he, SG, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt (R[4 * k + e]! * 3303); omega),
      val_mul]
    rfl

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
  rw [WP.block_append_iff]
  refine WP.mono (table_ok zetaTable (fun k hk => Nat.lt_trans (zetaTable_lt k hk) (by decide))
    (b := .x1) (by decide) fun k hk => by
      rw [hp.wr]
      exact in_regions (R := polyRegion (sP s₀)) (by simp) (contains_off (by omega) (by decide)))
    fun s₁ h₁ => WP.mono (vconsts_ok s₁) fun s₂ ⟨k₂, m₂, vc₂, _⟩ => ?_
  have fr : ∀ r ∈ [(⟨s₀.gpr .x1, 512⟩ : Region)], (polyRegion (fP s₀)).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.disj.sub_right (Region.sub_prefix (by decide))
  have k₂' := h₁.keep.trans k₂
  have st₂ : St s₀ s₂ := ⟨k₂'.rd, k₂'.wr, k₂'.sp, k₂'.get .x0, vc₂,
    fun k hk => by rw [m₂]; exact h₁.tab k hk⟩
  have p₂ : PolyIs s₂.mem (fP s₀) (P₀ s₀) := by
    rw [m₂]; exact polyIs_frame h₁.frame fr ⟨hp.red, rfl⟩
  have x1₂ : s₂.gpr .x1 = sP s₀ := by rw [k₂'.get .x1]
  -- the layer with `len = 2`
  refine WP.seq (WP.seq ?_)
  rw [← List.append_nil [mov .x2 .x0, Instr.addImm .x .x12 .x1 504, .movz .x .x5 32 0]]
  refine wp_scalar (by decide) (P := fun u => Keep [.x2, .x12, .x5] s₂ u ∧ u.mem = s₂.mem ∧
      u.gpr .x2 = s₂.gpr .x0 ∧ u.gpr .x12 = s₂.gpr .x1 + BitVec.ofNat 64 504 ∧ (u.gpr .x5).toNat = 32)
    (wp_mov fun u₁ h₁ e₁ => wp_addImm (by decide) fun u₂ h₂ e₂ => wp_movz fun u₃ h₃ e₃ =>
      wp_nil ⟨((h₁.keep.trans h₂.keep).trans h₃.keep).mono, by rw [h₃.mem, h₂.mem, h₁.mem],
        by rw [h₃.get .x2, h₂.get .x2, e₁], by rw [h₃.get .x12, e₂, h₁.get .x1],
        by rw [e₃]; rfl⟩) fun u₃ ⟨k₃, m₃, e2, e12, e5⟩ hv₃ => wp_nil ?_
  have i₀ : PInvI s₀ (P₀ s₀) 0 u₃ :=
    ⟨st₂.keep k₃ m₃ hv₃, by rw [e2, st₂.x0, coeffAddr]; exact (BitVec.add_zero _).symm,
      by rw [e12, x1₂], by rw [e5], by rw [m₃, Nat.mul_zero, nttInvLayerN_zero]; exact p₂⟩
  refine WP.mono (count_loop (by decide) (PInvI s₀ _) (fun c hc w hw => ipair_step hp hc hw) i₀)
    fun u₄ h₄ => ?_
  -- the layers with `len ≥ 4`
  refine WP.seq ?_
  rw [← List.append_nil [Instr.movz .x .x11 1 0, .addImm .x .x12 .x12 4, .movz .x .x13 32 0,
    .movz .x .x14 6 0]]
  refine wp_scalar (by decide) (P := fun u => Keep [.x11, .x12, .x13, .x14] u₄ u ∧ u.mem = u₄.mem ∧
      (u.gpr .x11).toNat = 1 ∧ u.gpr .x12 = u₄.gpr .x12 + BitVec.ofNat 64 4 ∧ (u.gpr .x13).toNat = 32 ∧
      (u.gpr .x14).toNat = 6)
    (wp_movz fun u₁ h₁ e₁ => wp_addImm (by decide) fun u₂ h₂ e₂ => wp_movz fun u₃ h₃ e₃ =>
      wp_movz fun u₅ h₅ e₅ => wp_nil ⟨(((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₅.keep).mono,
        by rw [h₅.mem, h₃.mem, h₂.mem, h₁.mem], by rw [h₅.get .x11, h₃.get .x11, h₂.get .x11, e₁]; rfl,
        by rw [h₅.get .x12, h₃.get .x12, e₂, h₁.get .x12], by rw [h₅.get .x13, e₃]; rfl,
        by rw [e₅]; rfl⟩) fun u₅ ⟨k₅, m₅, e11, e12', e13, e14⟩ hv₅ => wp_nil ?_
  have o₀ : OInvI s₀ 0 u₅ := by
    refine ⟨h₄.st.keep k₅ m₅ hv₅, by rw [e11], ?_, by rw [e13], by rw [e14], ?_⟩
    · rw [e12', h₄.x12, ptr_add]
    · have e : (nttInvLens.take (0 + 1)).foldl nttInvLayer (P₀ s₀) = nttInvLayerN (P₀ s₀) 2 (2 * 32) := by
        simp only [nttInvLens, List.take, List.foldl, nttInvLayer]
      rw [m₅, e]; exact h₄.poly
  refine WP.seq (WP.mono (count_loop (by decide) (OInvI s₀) (fun i hi u h => ilayer_step hp hi h) o₀)
    fun u₆ h₆ => ?_)
  -- the multiplication by 3303
  refine WP.seq ?_
  show WP isa (.block ([Instr.movz .x .x17 3303 0] ++ (.vop (.dup .s4 .v18 .x17) ::
    ([mov .x2 .x0, .movz .x .x5 64 0] ++ [])))) u₆ _
  refine wp_scalar (by decide) (P := fun u => Keep [.x17] u₆ u ∧ u.mem = u₆.mem ∧ (u.gpr .x17).toNat = 3303)
    (wp_movz fun u₇ h₇ e₇ => wp_nil ⟨h₇.keep, h₇.mem, by rw [e₇]; rfl⟩) fun u₇ ⟨k₇, m₇, e17⟩ hv₇ => ?_
  refine wp_vop (d := .v18) rfl fun u₈ h₈ => ?_
  refine wp_scalar (by decide) (P := fun u => Keep [.x2, .x5] u₈ u ∧ u.mem = u₈.mem ∧
      u.gpr .x2 = u₈.gpr .x0 ∧ (u.gpr .x5).toNat = 64)
    (wp_mov fun u₉ h₉ e₉ => wp_movz fun u₁₀ h₁₀ e₁₀ => wp_nil ⟨(h₉.keep.trans h₁₀.keep).mono,
      by rw [h₁₀.mem, h₉.mem], by rw [h₁₀.get .x2, e₉], by rw [e₁₀]; rfl⟩)
    fun u₁₀ ⟨k₁₀, m₁₀, e2', e5'⟩ hv₁₀ => wp_nil ?_
  have st₁₀ : St s₀ u₁₀ := ((h₆.st.keep k₇ m₇ hv₇).vchg h₈.chg).keep k₁₀ m₁₀ hv₁₀
  have hR : PolyIs u₁₀.mem (fP s₀) (nttInvLens.foldl nttInvLayer (P₀ s₀)) := by
    rw [m₁₀, h₈.mem, m₇]; exact h₆.poly
  have i₁ : SInv s₀ (nttInvLens.foldl nttInvLayer (P₀ s₀)) 0 u₁₀ := by
    refine ⟨st₁₀, ?_, ?_, by rw [e5'], fun i hi => ?_⟩
    · rw [hv₁₀, h₈.v]
      exact lanes_dup.congr fun _ _ => by rw [BitVec.toNat_setWidth, e17]
    · rw [e2', h₈.gpr, k₇.get .x0, h₆.st.x0, coeffAddr]; exact (BitVec.add_zero _).symm
    · rw [ite_eq_right (Nat.not_lt_zero i), polyIs_coeffAt hR (show i < n from hi), SO]
  refine WP.mono (count_loop (by decide) (SInv s₀ _) (fun k hk v hv => scale_step hp hk hv) i₁)
    fun s' hs' => ⟨hs'.st.sp, ?_⟩
  show PolyIs s'.mem (fP s₀) (nttInv (P₀ s₀))
  refine CoeffsUpTo.polyIs hs'.out fun i hi => ?_
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
