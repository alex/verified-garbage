import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Seed

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (Only only_write wp_add)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (tailAdd)

theorem tailAdd_ok (s : State) :
    WP isa (.block tailAdd) s fun t => Only [.x6,.x7,.x9] s t ∧
      t.gpr .x6 = s.gpr .x6 + 0x1f0000 ∧ t.gpr .x7 = s.gpr .x7 + 0x1f0000 := by
  unfold tailAdd
  refine VG.Proof.Sha3.AArch64.WP.cons (s' := s.write .x .x9 0x1f0000) rfl ?_
  have h1 := only_write s .x .x9 0x1f0000
  refine wp_add fun s2 h2 e2 => wp_add fun s3 h3 e3 => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ((h1.trans h2).trans h3).mono (by simp)
  · rw [h3.get .x6,e2,h1.get .x6,VG.AArch64.RegUpd.gpr_write_self]
    rfl
  · rw [e3,h2.get .x7,h1.get .x7,h2.get .x9,VG.AArch64.RegUpd.gpr_write_self]
    rfl
end VG.Proof.MlDsa.AArch64.Sample.Rej4
