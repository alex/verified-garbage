import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.ProArgs

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (pro oSave)

theorem pro_ok {σ : State} (hp : Pre σ) : WP isa (.block pro) σ (Env σ) := by
  unfold pro
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (saveG_ok hp) fun s1 ⟨h1,hf1,hg1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (saveV_ok hp h1.wr (by rw [h1.gpr]; rfl)) fun s2 ⟨h2,hv2,hf2,hvsave⟩ => ?_
  refine WP.mono (proArgs_ok s2) fun t ⟨h3,e19,e20,e21⟩ => ?_
  refine ⟨h3.rd.trans (h2.rd.trans h1.rd),h3.wr.trans (h2.wr.trans h1.wr),
    h3.sp.trans (h2.sp.trans h1.sp),?_,?_,?_,?_,?_,?_,?_⟩
  · rw [e19,h2.gpr .x2 (by decide),h1.gpr]; rfl
  · rw [e20,h2.gpr .x0 (by decide),h1.gpr]; rfl
  · rw [e21,h2.gpr .x1 (by decide),h1.gpr]; rfl
  · rw [h3.get .x30,h2.gpr .x30 (by decide),h1.gpr]
  · intro i hi
    rw [h3.mem]
    have hd : (⟨at' σ (oSave+8*i),8⟩ : Region).Disjoint (vSaveR σ) :=
      Offset.disjoint (scr σ) (d := oSave+8*i) (n := 8) (e := oSave+80) (k := 64)
        (by omega) (by dsimp only [oSave]; omega) (by decide)
    rw [hf2.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)]
    exact hg1 i hi
  · intro i hi
    rw [h3.mem,hvsave i hi,h1.vec]
  · rw [h3.mem]
    exact (hf1.sub (fun r hr => by rw [List.mem_singleton.mp hr]; exact
      ⟨scrR σ,by simp,Offset.sub_base (scr σ) (d := oSave) (n := 144) (k := 8192) (by decide)⟩)).trans
      (hf2.sub (fun r hr => by rw [List.mem_singleton.mp hr]; exact
        ⟨scrR σ,by simp,Offset.sub_base (scr σ) (d := oSave+80) (n := 64) (k := 8192) (by decide)⟩))
end VG.Proof.MlDsa.AArch64.Sample.Rej4
