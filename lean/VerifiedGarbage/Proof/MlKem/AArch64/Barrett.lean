import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.Ntt
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Impl.MlKem.AArch64.Ntt

/-!
# ML-KEM on AArch64: Barrett reduction and the tables

Untrusted: everything here is checked by Lean. `barrett` computes
`barrett64` (`Proof/MlKem/Arith.lean`) of a value less than `2³²`, for any
registers; `table` stores a table of 128 `u32`s; the tables of the code are
those of the standard (`zetaTable_eq`, `gammaTable_eq`).
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem (q)

theorem zetaTable_eq : zetaTable = zetas := rfl

theorem gammaTable_eq : gammaTable = gammas := rfl

theorem zetaTable_lt : ∀ k < 128, zetaTable.getD k 0 < q := by decide +kernel

theorem gammaTable_lt : ∀ k < 128, gammaTable.getD k 0 < q := by decide +kernel

/-- `barrett d t cr qr`: `d ← barrett64 d` for `d < 2³²`. -/
theorem barrett_ok {d t cr qr : Reg} (hdt : d ≠ t) (htq : t ≠ qr) {is : List Instr} {s : State} {Q : State → Prop} {x : Nat}
    (hx : x < 2 ^ 32) (hd : (s.gpr d).toNat = x) (hc : (s.gpr cr).toNat = 1290167)
    (hq : (s.gpr qr).toNat = q)
    (k : ∀ s', Only [d, t] s s' → (s'.gpr d).toNat = barrett64 x → WP isa (.block is) s' Q) :
    WP isa (.block (barrett d t cr qr ++ is)) s Q := by
  obtain ⟨b1, b2⟩ := barrett64_bounds hx
  refine wp_mul fun s₁ h₁ e₁ => wp_lsr (by decide) fun s₂ h₂ e₂ => wp_mul fun s₃ h₃ e₃ =>
    wp_sub fun s₄ h₄ e₄ => k s₄ ((((h₁.trans h₂).trans h₃).trans h₄).mono (by simp)) ?_
  have v₁ : (s₁.gpr t).toNat = x * 1290167 := by
    rw [e₁, toNat_mul_n (by rw [hd, hc]; exact b1), hd, hc]
  have v₂ : (s₂.gpr t).toNat = barrett64Quot x := by
    rw [e₂, toNat_lsr, v₁]; rfl
  have q₂ : (s₂.gpr qr).toNat = q := by
    rw [h₂.get qr (not_mem_one htq.symm), h₁.get qr (not_mem_one htq.symm), hq]
  have v₃ : (s₃.gpr t).toNat = barrett64Quot x * q := by
    rw [e₃, toNat_mul_n (by rw [v₂, q₂]; exact Nat.lt_of_le_of_lt b2 (by omega)), v₂, q₂]
  have d₃ : (s₃.gpr d).toNat = x := by
    rw [h₃.get d (not_mem_one hdt), h₂.get d (not_mem_one hdt), h₁.get d (not_mem_one hdt), hd]
  rw [e₄, toNat_sub_n (by rw [d₃, v₃]; exact b2), d₃, v₃]
  rfl

/-- `barrett` then `csub`: `d ← d mod q` for `d < 2³²`. -/
theorem reduce_ok {d t cr qr : Reg} (hdt : d ≠ t) (hdq : d ≠ qr) (htq : t ≠ qr) {is : List Instr} {s : State} {Q : State → Prop} {x : Nat}
    (hx : x < 2 ^ 32) (hd : (s.gpr d).toNat = x) (hc : (s.gpr cr).toNat = 1290167)
    (hq : (s.gpr qr).toNat = q)
    (k : ∀ s', Only [d, t] s s' → (s'.gpr d).toNat = x % q → WP isa (.block is) s' Q) :
    WP isa (.block (barrett d t cr qr ++ (csub d t qr ++ is))) s Q :=
  barrett_ok hdt htq hx hd hc hq fun s₁ h₁ e₁ =>
    csub_ok hdt hdq htq (barrett64_lt hx) e₁
      (by rw [h₁.get qr (not_mem_two hdq.symm htq.symm), hq]) fun s₂ h₂ e₂ =>
      k s₂ ((h₁.trans h₂).mono (by simp)) (by rw [e₂, reduce64 hx])

/-- The constants: `x9 = q`, `x10 = 1290167`. -/
theorem consts_ok (s : State) :
    WP isa (.block consts) s fun s' => Only [.x9, .x10] s s' ∧ (s'.gpr .x9).toNat = q ∧
      (s'.gpr .x10).toNat = 1290167 := by
  unfold consts
  refine wp_movz fun s₁ h₁ e₁ => ?_
  rw [← List.append_nil (movImm _ _)]
  refine wp_movImm fun s₂ h₂ e₂ => wp_nil ⟨(h₁.trans h₂).mono, by rw [h₂.get .x9, e₁]; rfl, by
    rw [e₂]; rfl⟩

/-! ## Tables -/

/-- After the first `k` entries of a table. -/
structure TabInv (T : List Nat) (b : Reg) (s₀ : State) (k : Nat) (s : State) : Prop where
  keep : Keep [.x9] s₀ s
  frame : Frame [⟨s₀.gpr b, 512⟩] s₀.mem s.mem
  tab : ∀ j < k, s.mem.readW (s₀.gpr b + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (T.getD j 0)

/-- `table T b` stores the table `T` at `b`. -/
theorem table_ok (T : List Nat) (hT : ∀ k < 128, T.getD k 0 < 65536) {b : Reg} (hb : b ≠ .x9)
    {s₀ : State} (hin : ∀ k < 128, InRegions s₀.wr (s₀.gpr b + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (table T b)) s₀ (TabInv T b s₀ 128) := by
  refine wp_range_flatMap (M := isa) (TabInv T b s₀) (fun k s hk h => ?_) 128 (Nat.le_refl _) s₀
    ⟨Keep.refl _ _, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have hbk : s.gpr b = s₀.gpr b := h.keep.get b (not_mem_one hb)
  refine wp_movz fun s₁ h₁ e₁ => wp_strw (a := s₀.gpr b + BitVec.ofNat 64 (4 * k))
    ⟨by omega, by omega⟩ (by rw [h₁.get b (not_mem_one hb), hbk]) (by rw [h₁.wr, h.keep.wr]; exact hin k hk)
    fun s₂ h₂ => wp_nil ?_
  have v : (s₁.gpr .x9).setWidth 32 = BitVec.ofNat 32 (T.getD k 0) := by
    refine setWidth32_of_toNat ?_
    rw [e₁, toNat_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hT k hk)]
  refine ⟨(h.keep.trans (h₁.keep.trans h₂.keep)).mono, ?_, fun j hj => ?_⟩
  · rw [h₂.mem, h₁.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))
  · rw [h₂.mem, h₁.mem, v]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.tab j (by omega)

end VG.Proof.MlKem.AArch64
