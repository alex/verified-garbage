import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.MlKem.AArch64 (wp_vop VChg)
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep constant_ok constantLow_RC)

theorem iota_word (A : Spec.Sha3.State) (r : Nat) {i : Nat} (hi : i < 25) :
    (Spec.Sha3.iota A r)[i]! = if i = 0 then A[0]! ^^^ Spec.Sha3.RC r else A[i]! := by
  rw [VG.Proof.Sha3.getElem!_eq _ hi]
  unfold Spec.Sha3.iota
  rw [Vector.getElem_set]
  by_cases he : i = 0
  · subst i
    rw [ite_eq_left rfl,ite_eq_left rfl,VG.Proof.Sha3.getElem!_eq A (by decide)]
  · rw [ite_eq_right (Ne.symm he),ite_eq_right he,VG.Proof.Sha3.getElem!_eq A hi]

/-- Broadcast the round constant into both independent states. -/
theorem iota_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) (r : Nat)
    (hr : s.gpr .x16 = Spec.Sha3.RC r) :
    WP isa (.block iota) s fun s' => VChg allV s s' ∧ Pairs s' (Spec.Sha3.iota A r) (Spec.Sha3.iota B r) := by
  unfold iota
  refine wp_vop (d := .v25) rfl fun s₁ h1 => wp_vop (d := .v0) rfl fun s₂ h2 =>
    WP.block_nil_iff.mpr ⟨(h1.chg.trans h2.chg).mono (fun v _ => allV_mem v),?_⟩
  intro i hi
  rw [iota_word A r hi,iota_word B r hi]
  by_cases he : i = 0
  · subst i
    rw [ite_eq_left rfl,ite_eq_left rfl]
    change s₂.v .v0 = _
    rw [h2.v,h1.get .v0,h1.v,hr]
    have hp0 : s.v .v0 = ofVDwords A[0]! B[0]! := hp 0 (by decide)
    change s.v .v0 ^^^ ofVDwords (Spec.Sha3.RC r) (Spec.Sha3.RC r) = _
    rw [hp0,pair_xor]
  · have h0 : vreg i ≠ VReg.v0 := by
      change vreg i ≠ vreg 0
      rw [ne_eq,vreg_inj i (by omega) 0 (by decide)]; exact he
    have h25 : vreg i ≠ VReg.v25 := by
      change vreg i ≠ vreg 25
      rw [ne_eq,vreg_inj i (by omega) 25 (by decide)]; omega
    rw [ite_eq_right he,ite_eq_right he,h2.get _ h0,h1.get _ h25]
    exact hp i hi

theorem vchg_core {s s' : State} {rs : List VReg} (h : VChg rs s s') : CoreKeep s s' :=
  ⟨fun r _ => congrFun h.gpr r,h.mem,h.rd,h.wr,h.sp⟩

/-- One portable NEON round of Keccak, on two independent states. -/
theorem round_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) {r : Nat} (hr : r < 24) :
    WP isa (.block (round r)) s fun s' => CoreKeep s s' ∧ Pairs s' (Spec.Sha3.rnd A r) (Spec.Sha3.rnd B r) := by
  unfold round
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constant_ok (Spec.Sha3.RC r) s) fun s₁ ⟨h1,hv1,hc1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (theta_ok (A := A) (B := B) (by intro i hi; rw [hv1]; exact hp i hi)) fun s₂ ⟨h2,hp2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rhoPi_ok hp2) fun s₃ ⟨h3,hp3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (chi_ok hp3) fun s₄ ⟨h4,hp4⟩ => ?_
  refine WP.mono (iota_ok hp4 r (by rw [h4.gpr,h3.gpr,h2.gpr,hc1,constantLow_RC r hr]))
    fun s₅ ⟨h5,hp5⟩ => ⟨h1.trans ((vchg_core h2).trans ((vchg_core h3).trans ((vchg_core h4).trans (vchg_core h5)))),hp5⟩
end VG.Proof.Sha3.AArch64.Neon
