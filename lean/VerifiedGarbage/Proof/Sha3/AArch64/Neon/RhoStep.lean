import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Theta

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)

/-- Install a rotated predecessor while saving the displaced state word. -/
theorem rhoPiStep_ok {s : State} {j k : Nat} (hj : j < 25) (hk0 : 0 < k) (hk : k < 64) :
    WP isa (.block (rhoPiStep (j,k))) s fun s' => VChg [vreg j,.v25,.v26] s s' ∧
      s'.v (vreg j) = ofVDwords ((vdword (s.v .v25) 0).rotateLeft k)
        ((vdword (s.v .v25) 1).rotateLeft k) ∧ s'.v .v25 = s.v (vreg j) := by
  have h25 : vreg j ≠ VReg.v25 := by
    change vreg j ≠ vreg 25
    rw [ne_eq,vreg_inj j (by omega) 25 (by decide)]; omega
  have h26 : vreg j ≠ VReg.v26 := by
    change vreg j ≠ vreg 26
    rw [ne_eq,vreg_inj j (by omega) 26 (by decide)]; omega
  unfold rhoPiStep
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v26) rfl fun s₁ h1 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rol_ok h25 hk0 hk) fun s₂ ⟨h2,v2⟩ => ?_
  refine wp_vop (d := .v25) rfl fun s₃ h3 => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ((h1.chg.trans h2).trans h3.chg).mono (by
      intro r hr
      simp only [List.mem_append,List.mem_singleton] at hr
      rcases hr with (rfl | rfl) | rfl <;> simp)
  · rw [h3.get _ h25,v2,h1.get .v25]
  · rw [h3.v,h2.get .v26 (by simp only [List.mem_singleton]; exact Ne.symm h26),h1.v]
end VG.Proof.Sha3.AArch64.Neon
