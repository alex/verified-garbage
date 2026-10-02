import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqPair

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_addImm wp_subImm)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (advance)

theorem advance_ok (s : State) : WP isa (.block advance) s fun t => Only [.x24,.x25,.x26,.x27,.x28] s t ∧
    (∀ k < 4,t.gpr (bReg k) = s.gpr (bReg k)+168) ∧ t.gpr .x28 = s.gpr .x28-1 := by
  unfold advance
  refine wp_addImm (by decide) fun s1 h1 e1 => wp_addImm (by decide) fun s2 h2 e2 =>
    wp_addImm (by decide) fun s3 h3 e3 => wp_addImm (by decide) fun s4 h4 e4 =>
      wp_subImm (by decide) fun t h5 e5 => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ((((h1.trans h2).trans h3).trans h4).trans h5).mono (by simp)
  · intro k hk
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · change t.gpr .x24 = s.gpr .x24+168
      rw [h5.get .x24,h4.get .x24,h3.get .x24,h2.get .x24,e1]; rfl
    · change t.gpr .x25 = s.gpr .x25+168
      rw [h5.get .x25,h4.get .x25,h3.get .x25,e2,h1.get .x25]; rfl
    · change t.gpr .x26 = s.gpr .x26+168
      rw [h5.get .x26,h4.get .x26,e3,h2.get .x26,h1.get .x26]; rfl
    · change t.gpr .x27 = s.gpr .x27+168
      rw [h5.get .x27,e4,h3.get .x27,h2.get .x27,h1.get .x27]; rfl
  · rw [e5,h4.get .x28,h3.get .x28,h2.get .x28,h1.get .x28]; rfl
end VG.Proof.MlDsa.AArch64.Sample.Rej4
