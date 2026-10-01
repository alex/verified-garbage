import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddSetup
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMain

/-! Untrusted: full-width multiply-add followed by subgroup reduction. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64
open VG.Spec.Ed25519 (bytesAt decodeLE)

def scalarMulAddLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 32⟩, ⟨s.gpr .x2, 32⟩, ⟨s.gpr .x3, 32⟩] ∧
    s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x4, 8192⟩] ∧
    (⟨s.gpr .x1, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (⟨s.gpr .x2, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (⟨s.gpr .x3, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64
  post s t := bytesAt t.mem (s.gpr .x0) 32 = Spec.Ed25519.scalarMulAdd
    (bytesAt s.mem (s.gpr .x1) 32) (bytesAt s.mem (s.gpr .x2) 32) (bytesAt s.mem (s.gpr .x3) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4

theorem MulAddPre.of {s : State} (h : scalarMulAddLocal.pre s) : MulAddPre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem scalarMulAdd_correct {s : State} (hs : MulAddPre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  apply WP.withPreservedV (hc := by decide +kernel)
  have hw : (⟨s.gpr .x4, 8192⟩ : Region) ∈ s.wr := by rw [hs.wr]; simp
  rw [scalarMulAdd]
  refine WP.seq (WP.mono (mulAddSetup_ok hs) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (wideAccumulate_ok ⟨h₁.base, h₁.wr ▸ hw, hs.nowrap⟩
    (by constructor <;> decide) (by constructor <;> decide)) fun s₂ ⟨v₂, k₂⟩ => ?_)
  have prod₂ : wideValue s₂ = fe s.mem (s.gpr .x1) 0 +
      fe s.mem (s.gpr .x2) 0 * fe s.mem (s.gpr .x3) 0 := by
    rw [v₂, h₁.value, h₁.left, h₁.right]
  have base₂ : s₂.gpr .x0 = s.gpr .x4 := (k₂.gpr _ (by decide)).trans h₁.base
  have wr₂ : s₂.wr = s.wr := k₂.wr.trans h₁.wr
  apply WP.seq
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeWide_ok ⟨base₂, wr₂ ▸ hw, hs.nowrap⟩) fun s₃ ⟨v₃, g₃, rd₃, wr₃, sp₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduceArgs_ok s₃) fun s₄ ⟨x1₄, x2₄, x0₄, k₄⟩ => ?_
  refine WP.mono (scalarInit_ok s₄) fun s₅ ⟨b₅, v₅, z₅, one₅, k₅⟩ => ?_
  have x1₅ : s₅.gpr .x1 = off (s.gpr .x4) 128 := by rw [k₅.gpr _ (by decide), x1₄, g₃, base₂]
  have x2₅ : s₅.gpr .x2 = s.gpr .x4 := by rw [k₅.gpr _ (by decide), x2₄, g₃, base₂]
  have x0₅ : s₅.gpr .x0 = s.gpr .x0 := by
    rw [k₅.gpr _ (by decide), x0₄, g₃, k₂.gpr _ (by decide), h₁.out]
  have wr₅ : s₅.wr = s.wr := by rw [k₅.wr, k₄.wr, wr₃, wr₂]
  have read₅ : ∀ n < 64, InRegions (s₅.rd ++ s₅.wr) (s₅.gpr .x1 + BitVec.ofNat 64 n) 1 := by
    intro n hn
    refine ⟨⟨s.gpr .x4, 8192⟩, List.mem_append_right _ (wr₅ ▸ hw), ?_⟩
    rw [x1₅, Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
  have sv₅ : Saved (s.gpr .x4) s.gpr s₅.mem := by
    have sv₂ : Saved (s.gpr .x4) s.gpr s₂.mem := by rw [k₂.mem]; exact h₁.saved
    rw [k₅.mem, k₄.mem]; exact sv₂.outside o₃ (by decide)
  apply WP.seq
  refine WP.mono (scalarLoop_ok s₅ b₅ v₅ read₅ z₅ one₅) fun s₆ ⟨v₆, k₆⟩ => ?_
  have wr₆ : s₆.wr = s.wr := k₆.wr.trans wr₅
  have val₆ : scalarValue s₆ = (fe s.mem (s.gpr .x1) 0 +
      fe s.mem (s.gpr .x2) 0 * fe s.mem (s.gpr .x3) 0) % Spec.Ed25519.L := by
    rw [v₆, x1₅, k₅.mem, k₄.mem, v₃, prod₂]
  rw [scalarFinish, WP.block_append_iff]
  refine WP.mono (scalarRestore_ok (g := s.gpr) ((k₆.gpr _ (by decide)).trans x2₅) (wr₆ ▸ hw)
    (by rw [k₆.mem]; exact sv₅)) fun s₇ ⟨rest₇, k₇⟩ => ?_
  have x0₇ : s₇.gpr .x0 = s.gpr .x0 :=
    (k₇.gpr _ (by decide)).trans ((k₆.gpr _ (by decide)).trans x0₅)
  have hwo : (⟨s.gpr .x0, 32⟩ : Region) ∈ s₇.wr := by rw [k₇.wr, wr₆, hs.wr]; simp
  refine WP.mono (scalarOut_ok x0₇ hwo) fun t ht => ?_
  subst t
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rest₇ (.x19, 0) (by decide)
    · exact rest₇ (.x20, 8) (by decide)
    · exact rest₇ (.x21, 16) (by decide)
    · exact rest₇ (.x22, 24) (by decide)
    · exact rest₇ (.x23, 32) (by decide)
    · exact rest₇ (.x24, 40) (by decide)
    all_goals
      rw [k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide),
        k₄.gpr _ (by decide), g₃, k₂.gpr _ (by decide), h₁.preserved _ (by decide)]
  · exact k₇.sp.trans (k₆.sp.trans (k₅.sp.trans (k₄.sp.trans (sp₃.trans (k₂.sp.trans h₁.sp)))))
  · change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, Spec.Ed25519.scalarMulAdd, encodeLE_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    have v₇ : scalarValue s₇ = scalarValue s₆ := by
      simp only [scalarValue, k₇.gpr .x4 (by decide), k₇.gpr .x5 (by decide), k₇.gpr .x6 (by decide),
        k₇.gpr .x7 (by decide)]
    change scalarValue s₇ = _
    rw [v₇, val₆]
    have hd (p : Addr) : decodeLE (bytesAt s.mem p 32) = fe s.mem p 0 := by
      have h := decodeLE_words s.mem p 0
      rw [show off p 0 = p from BitVec.add_zero p] at h
      exact h
    rw [hd, hd, hd]

end VG.Proof.Ed25519.AArch64
