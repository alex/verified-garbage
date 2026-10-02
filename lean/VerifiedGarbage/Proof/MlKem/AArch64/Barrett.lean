import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.Ntt
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Impl.MlKem.AArch64.Ntt

/-!
# ML-KEM on AArch64: the tables

`table` stores a table of 128 `u32`s; the tables of the code are those of the
standard (`zetaTable_eq`, `gammaTable_eq`).
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem (q)

theorem zetaTable_eq : zetaTable = zetas := rfl

theorem gammaTable_eq : gammaTable = gammas := rfl

theorem zetaTable_lt : ∀ k < 128, zetaTable.getD k 0 < q := by decide +kernel

theorem gammaTable_lt : ∀ k < 128, gammaTable.getD k 0 < q := by decide +kernel

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
