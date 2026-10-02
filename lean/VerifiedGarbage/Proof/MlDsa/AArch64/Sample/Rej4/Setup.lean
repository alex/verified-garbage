import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Init
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPhase

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_mov wp_addImm wp_movz)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (setup oBuf)

theorem setup_shape (s : State) : WP isa (.block setup) s fun t =>
    Only [.x22,.x23,.x24,.x25,.x26,.x27,.x28] s t ∧ t.gpr .x22 = s.gpr .x19 ∧
      t.gpr .x23 = s.gpr .x19+BitVec.ofNat 64 400 ∧
      (∀ k < 4,t.gpr (bReg k) = s.gpr .x19+BitVec.ofNat 64 (oBuf+1008*k)) ∧ t.gpr .x28 = 6 := by
  unfold setup
  refine wp_mov fun s1 h1 e1 => wp_addImm (by decide) fun s2 h2 e2 =>
    wp_addImm (by decide) fun s3 h3 e3 => wp_addImm (by decide) fun s4 h4 e4 =>
      wp_addImm (by decide) fun s5 h5 e5 => wp_addImm (by decide) fun s6 h6 e6 =>
        wp_movz fun t h7 e7 => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_,?_⟩
  · exact ((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).mono (by simp)
  · rw [h7.get .x22,h6.get .x22,h5.get .x22,h4.get .x22,h3.get .x22,h2.get .x22,e1]
  · rw [h7.get .x23,h6.get .x23,h5.get .x23,h4.get .x23,h3.get .x23,e2,h1.get .x19]
  · intro k hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · change t.gpr .x24 = _
      rw [h7.get .x24,h6.get .x24,h5.get .x24,h4.get .x24,e3,h2.get .x19,h1.get .x19]
    · change t.gpr .x25 = _
      rw [h7.get .x25,h6.get .x25,h5.get .x25,e4,h3.get .x19,h2.get .x19,h1.get .x19]
    · change t.gpr .x26 = _
      rw [h7.get .x26,h6.get .x26,e5,h4.get .x19,h3.get .x19,h2.get .x19,h1.get .x19]
    · change t.gpr .x27 = _
      rw [h7.get .x27,e6,h5.get .x19,h4.get .x19,h3.get .x19,h2.get .x19,h1.get .x19]
  · rw [e7]; rfl

/-- Enter the six-block loop after absorbing all four seeds. -/
theorem setup_ok {σ s : State} (he : Env σ s)
    (hp0 : VG.Proof.Sha3.AArch64.Neon.PairAt s.mem (stateP σ 0) (A0 σ 0) (A0 σ 1))
    (hp1 : VG.Proof.Sha3.AArch64.Neon.PairAt s.mem (stateP σ 1) (A0 σ 2) (A0 σ 3)) :
    WP isa (.block setup) s (Phase σ 0 0) := by
  refine WP.mono (setup_shape s) fun t ⟨ht,e22,e23,hptr,e28⟩ => ?_
  refine ⟨he.lowStep (rs := []) (by rw [ht.mem]; exact Frame.refl _ _) (by simp) ht.rd ht.wr ht.sp
    (fun r hr => ht.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),?_,?_,?_,?_,?_,?_⟩
  · rw [e22,he.x19]
    unfold stateP at'
    rw [Nat.mul_zero]
    exact (BitVec.add_zero _).symm
  · rw [e23,he.x19]; rfl
  · intro k hk
    rw [hptr k hk,he.x19]
    unfold bufAt at'
    rw [Nat.mul_zero,Nat.add_zero]
  · rw [e28]; rfl
  · intro p hp
    rw [ht.mem]
    rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
    · exact hp0
    · exact hp1
  · intro k _ j hj
    exact False.elim (by simp at hj)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
