import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SaveV

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_mov)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (proArgs)

theorem proArgs_ok (s : State) :
    WP isa (.block proArgs) s fun t => Only [.x19,.x20,.x21] s t ∧
      t.gpr .x19 = s.gpr .x2 ∧ t.gpr .x20 = s.gpr .x0 ∧ t.gpr .x21 = s.gpr .x1 := by
  unfold proArgs
  refine wp_mov fun s1 h1 e1 => wp_mov fun s2 h2 e2 => wp_mov fun t h3 e3 => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact ((h1.trans h2).trans h3).mono (by simp)
  · rw [h3.get .x19,h2.get .x19,e1]
  · rw [h3.get .x20,e2,h1.get .x0]
  · rw [e3,h2.get .x1,h1.get .x1]
end VG.Proof.MlDsa.AArch64.Sample.Rej4
