import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.RestoreG

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_mov wp_ldrx)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (epi oSave saved)

theorem epi_ok {σ s : State} (hp : Pre σ) (he : Env σ s) :
    WP isa (.block epi) s fun t => abiPreserved σ t ∧ t.mem = s.mem ∧ t.gpr .x0 = s.gpr .x27 ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  unfold epi
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine wp_mov fun s1 h1 e1 => WP.block_nil_iff.mpr ?_
  have he1 := he.lowStep (rs := []) (by rw [h1.mem]; exact Frame.refl _ _) (by simp)
    h1.rd h1.wr h1.sp (fun r hr => h1.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  rw [WP.block_append_iff]
  refine WP.mono (restoreV_ok hp he1) fun s2 ⟨h2,m2,v2⟩ => ?_
  have he2 := he1.lowStep (rs := []) (by rw [m2]; exact Frame.refl _ _) (by simp)
    h2.rd h2.wr h2.sp (fun r hr => h2.gpr r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  rw [WP.block_append_iff]
  refine WP.mono (restoreG_ok hp he2) fun s3 ⟨h3,g3⟩ => ?_
  refine wp_ldrx (a := at' σ oSave) ⟨by decide,by decide⟩ (by rw [h3.get .x19,he2.x19]; rfl)
    (in_scr_rd hp (h3.rd.trans he2.rd) (h3.wr.trans he2.wr) (d := oSave) (n := 8) (by decide))
    fun t h4 e4 => WP.block_nil_iff.mpr ⟨⟨?_,?_,?_⟩,?_,?_,?_,?_⟩
  · intro r hr
    have hs : ∀ r ∈ preserved,r = .x19 ∨ r = .x30 ∨ ∃ i < 9,r = saved[i+1]! := by decide
    rcases hs r hr with rfl | rfl | ⟨i,hi,rfl⟩
    · rw [e4,h3.mem,m2,h1.mem]
      exact he.savedG 0 (by decide)
    · rw [h4.get .x30,h3.get .x30,h2.gpr .x30 (by decide),he1.x30]
    · rw [h4.get (saved[i+1]!) (by simpa only [List.mem_singleton] using saved_ne19 i hi)]
      exact g3 i hi
  · exact h4.sp.trans (h3.sp.trans (h2.sp.trans he1.sp))
  · intro r hr
    have hs : ∀ r ∈ preservedV,∃ i < 8,r = VG.Impl.Sha3.AArch64.Sha3.Vector.vreg (8+i) := by decide
    obtain ⟨i,hi,rfl⟩ := hs r hr
    rw [h4.vcs _ hr,h3.vcs _ hr]
    exact v2 i hi
  · exact h4.mem.trans (h3.mem.trans (m2.trans h1.mem))
  · rw [h4.get .x0,h3.get .x0,h2.gpr .x0 (by decide),e1]
  · exact h4.rd.trans (h3.rd.trans (h2.rd.trans h1.rd))
  · exact h4.wr.trans (h3.wr.trans (h2.wr.trans h1.wr))
end VG.Proof.MlDsa.AArch64.Sample.Rej4
