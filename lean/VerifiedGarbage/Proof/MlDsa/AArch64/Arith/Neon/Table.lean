import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Step
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Table

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab)
open VG.Proof.MlKem.AArch64 (Keep wp_vop VChg)
open VG.Spec.MlDsa (q Zq zetas)

def TabZ (tab : Nat → Nat) (zt : Zq → Zq) : Prop :=
  ∀ k, tab k = (zt (zetas k)).val*2^32%q

theorem zetaTab_eq : TabZ zetaTab id := by
  intro k
  change zetaTab k = (Spec.MlDsa.zetas k).val*2^32%q
  rw [zetaTab,← zetaNat_eq,zetaNat,Nat.mod_mul_mod]

theorem negZetaTab_eq : TabZ negZetaTab (fun z => -z) := by
  intro k
  rw [negZetaTab,← negZetaNat_eq,negZetaNat,zetaNat]

theorem loadZ_ok (up : Bool) (s : State)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x3) 4) :
    WP isa (.block [.ldr .w .x6 .x3 0,stepZ up]) s fun s' =>
      ((s'.gpr .x6 = (s.mem.readW (s.gpr .x3) 32).setWidth 64 ∧
        s'.gpr .x3 = (if up then s.gpr .x3+4 else s.gpr .x3-4) ∧ s'.mem = s.mem) ∧
        Keep [.x6,.x3] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by cases up <;> rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by cases up <;> rfl) (hv := by cases up <;> rfl)
  cases up <;> arun [stepZ,hin] <;> rfl

/-- A full-width vector of the table's zeta for a large NTT block. -/
theorem zetas_large_ok {tab : Nat → Nat} {zt : Zq → Zq} (htz : TabZ tab zt)
    {len : Nat} (hl1 : len ≠ 1) (hl2 : len ≠ 2) (up : Bool) {s : State} {p : Addr} {k : Nat}
    (hk : k < 256) (h3 : s.gpr .x3 = coeffAddr p k) (ht : Tab tab s.mem p 256)
    (hp : pR p ∈ s.rd++s.wr) (hc : VConsts s) :
    WP isa (.block (Impl.MlDsa.AArch64.Arith.Neon.zetas len up)) s fun s' =>
      Zetas (s'.v .v18) (fun _ => zt (Spec.MlDsa.zetas k)) ∧ VConsts s' ∧
      s'.gpr .x3 = (if up then s.gpr .x3+4 else s.gpr .x3-4) ∧ s'.mem = s.mem ∧
      Keep [.x6,.x3] s s' := by
  simp only [Impl.MlDsa.AArch64.Arith.Neon.zetas,hl1,hl2,ite_false]
  have hread : (s.mem.readW (s.gpr .x3) 32).toNat = (zt (Spec.MlDsa.zetas k)).val*2^32%q := by
    rw [h3,← coeffAt_eq,ht k hk,BitVec.toNat_ofNat,htz k]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  change WP isa (.block ([.ldr .w .x6 .x3 0,stepZ up] ++ [.vop (.dup .s4 .v18 .x6)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (loadZ_ok up s (by rw [h3]; exact ⟨_,hp,coeff_contains _ hk⟩))
    fun s₁ ⟨⟨⟨h6,h3',hm⟩,h₁⟩,hv⟩ => wp_vop (d := .v18) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨?_, ?_, by rw [h₂.gpr]; exact h3', by rw [h₂.mem]; exact hm,
        (h₁.trans h₂.keep).mono⟩
  · intro e he
    rw [h₂.v]
    change (vword (ofVWords ((s₁.gpr .x6).setWidth 32) ((s₁.gpr .x6).setWidth 32)
      ((s₁.gpr .x6).setWidth 32) ((s₁.gpr .x6).setWidth 32)) e).toNat = _
    rw [VG.Proof.MlKem.AArch64.vword_dup_s4 _ he,h6,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq,hread]
  · exact (⟨by rw [hv]; exact hc.q, by rw [hv]; exact hc.qi⟩ : VConsts s₁).chg h₂.chg
end VG.Proof.MlDsa.AArch64.Arith.Neon
