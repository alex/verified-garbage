import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.AArch64.Codec
import VerifiedGarbage.TCB.AArch64.Target

/-! Untrusted: complete scalar reduction, including preservation of the AAPCS64 ABI. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Spec.Ed25519 (bytesAt)

def scalarReduceLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 64⟩] ∧ s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩] ∧
    (⟨s.gpr .x1, 64⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩
  post s t := bytesAt t.mem (s.gpr .x0) 32 =
    Spec.Ed25519.scalarReduce (bytesAt s.mem (s.gpr .x1) 64)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

theorem scalarReduce_correct {s : State} (hs : scalarReduceLocal.pre s) :
    WP isa scalarReduce s fun t => abiPreserved s t ∧ scalarReduceLocal.post s t := by
  apply WP.withPreservedV (hc := by decide +kernel)
  obtain ⟨hr, hw, hd⟩ := hs
  have hws : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarReduce]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok rfl hws) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, o₁, sv₁⟩ => ?_
  refine WP.mono (scalarInit_ok s₁) fun s₂ ⟨b₂, v₂, z₂, one₂, k₂⟩ => ?_
  have x1₂ : s₂.gpr .x1 = s.gpr .x1 := (k₂.gpr _ (by decide)).trans (congrFun g₁ _)
  have x2₂ : s₂.gpr .x2 = s.gpr .x2 := (k₂.gpr _ (by decide)).trans (congrFun g₁ _)
  have x0₂ : s₂.gpr .x0 = s.gpr .x0 := (k₂.gpr _ (by decide)).trans (congrFun g₁ _)
  have read₂ : ∀ n < 64, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x1 + BitVec.ofNat 64 n) 1 := by
    intro n hn
    refine ⟨⟨s.gpr .x1, 64⟩, ?_, ?_⟩
    · rw [k₂.rd, rd₁, hr]; simp
    · rw [x1₂]; exact Offset.contains_base _ (by omega) (by omega)
  apply WP.seq
  refine WP.mono (scalarLoop_ok s₂ b₂ v₂ read₂ z₂ one₂) fun s₃ ⟨v₃, k₃⟩ => ?_
  have x2₃ : s₃.gpr .x2 = s.gpr .x2 := (k₃.gpr _ (by decide)).trans x2₂
  have wr₃ : s₃.wr = s.wr := k₃.wr.trans (k₂.wr.trans wr₁)
  have sv₃ : Saved (s.gpr .x2) s.gpr s₃.mem := by rw [k₃.mem, k₂.mem]; exact sv₁
  rw [scalarFinish, WP.block_append_iff]
  refine WP.mono (scalarRestore_ok x2₃ (wr₃ ▸ hws) sv₃) fun s₄ ⟨r₄, k₄⟩ => ?_
  have x0₄ : s₄.gpr .x0 = s.gpr .x0 :=
    (k₄.gpr _ (by decide)).trans ((k₃.gpr _ (by decide)).trans x0₂)
  have hwo : (⟨s.gpr .x0, 32⟩ : Region) ∈ s₄.wr := by rw [k₄.wr, wr₃, hw]; simp
  refine WP.mono (scalarOut_ok x0₄ hwo) fun t ht => ?_
  subst t
  refine ⟨⟨fun r hpres => ?_, k₄.sp.trans (k₃.sp.trans (k₂.sp.trans sp₁))⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hpres
    rcases hpres with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r₄ (.x19, 0) (by decide)
    · exact r₄ (.x20, 8) (by decide)
    · exact r₄ (.x21, 16) (by decide)
    · exact r₄ (.x22, 24) (by decide)
    · exact r₄ (.x23, 32) (by decide)
    · exact r₄ (.x24, 40) (by decide)
    all_goals
      rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), g₁]
  · change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, Spec.Ed25519.scalarReduce, encodeLE_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    change scalarValue s₄ = _
    have val₄ : scalarValue s₄ = scalarValue s₃ := by
      simp only [scalarValue, k₄.gpr .x4 (by decide), k₄.gpr .x5 (by decide),
        k₄.gpr .x6 (by decide), k₄.gpr .x7 (by decide)]
    rw [val₄, v₃, x1₂, k₂.mem, bytesAt_frame (scalarSave_frame o₁) hd]

end VG.Proof.Ed25519.AArch64
