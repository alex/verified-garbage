import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Layers

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.AArch64.Arith (inPlaceK Tab storeTab_ok movW_ok)
open VG.Proof.MlKem.AArch64 (Keep wp_vop wp_scalar)
open VG.Spec.MlDsa (Poly PolyIs polyAt)

theorem consts_ok (s : State) :
    WP isa (.block consts) s fun s' => VConsts s' ∧ s'.mem = s.mem ∧ Keep [.x9,.x10] s s' := by
  unfold consts
  simp only [List.append_assoc]
  refine wp_scalar (by rfl) (movW_ok .x9 8380417 s) fun s₁ ⟨⟨h9,hm1⟩,k1⟩ hv1 => ?_
  refine wp_scalar (by rfl) (movW_ok .x10 4236238847 s₁) fun s₂ ⟨⟨h10,hm2⟩,k2⟩ hv2 => ?_
  refine wp_vop (d := .v16) rfl fun s₃ h3 => wp_vop (d := .v17) rfl fun s₄ h4 =>
    WP.block_nil_iff.mpr ⟨⟨?_,?_⟩,by rw [h4.mem,h3.mem,hm2,hm1],
      (((k1.trans k2).trans h3.keep).trans h4.keep).mono⟩
  · rw [h4.get .v16,h3.v,k2.get .x9,h9]
    rfl
  · rw [h4.v,h3.gpr,h10]
    rfl

/-- Initialize the Montgomery table and constants without changing the input polynomial. -/
theorem pro_ok {s : State} {t : Poly → Poly} (hp : (inPlaceK t).pre s) (tab : Nat → Nat) :
    WP isa (.block (pro tab)) s fun s' =>
      PolyIs s'.mem (s.gpr .x0) (polyAt s.mem (s.gpr .x0)) ∧
      Tab tab s'.mem (s.gpr .x1) 256 ∧ VConsts s' ∧
      Frame [pR (s.gpr .x1)] s.mem s'.mem ∧ Keep [.x9,.x10] s s' := by
  unfold pro
  rw [WP.block_append_iff]
  refine WP.mono (storeTab_ok tab (b := .x1) (by decide) s (by rw [hp.2.1]; simp))
    fun s₁ ⟨ht,hf,k1⟩ => ?_
  refine WP.mono (consts_ok s₁) fun s₂ ⟨hc,hm2,k2⟩ =>
    ⟨?_,by rw [hm2]; exact ht,hc,by rw [hm2]; exact hf,(k1.trans k2).mono⟩
  rw [hm2]
  exact ⟨VG.Proof.MlDsa.Arith.reduced_frame hf (by simpa using hp.2.2.1) hp.2.2.2,
    VG.Proof.MlDsa.Arith.polyAt_frame hf (by simpa using hp.2.2.1)⟩
end VG.Proof.MlDsa.AArch64.Arith.Neon
