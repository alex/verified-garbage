import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Base

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oSave)

theorem Env.frameStep {σ s t : State} (he : Env σ s) {rs : List Region}
    (hf : Frame rs s.mem t.mem)
    (hsub : ∀ r ∈ rs, ∃ R ∈ [aR σ,scrR σ],Region.Sub r R)
    (hsave : ∀ r ∈ rs,(saveR σ).Disjoint r)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ [Reg.x19,.x20,.x21,.x30],t.gpr r = s.gpr r) : Env σ t := by
  refine ⟨hr.trans he.rd,hw.trans he.wr,hsp.trans he.sp,
    (hg .x19 (by simp)).trans he.x19,(hg .x20 (by simp)).trans he.x20,
    (hg .x21 (by simp)).trans he.x21,(hg .x30 (by simp)).trans he.x30,
    fun i hi => ?_,fun i hi => ?_,he.frame.trans (hf.sub hsub)⟩
  · have hc : (saveR σ).Contains (at' σ (oSave+8*i)) 8 :=
      Offset.contains (scr σ) (d := oSave+8*i) (e := oSave) (n := 8) (k := 144)
        (by omega) (by omega) (by decide)
    rw [hf.readW hc hsave (by decide)]
    exact he.savedG i hi
  · have hc : (saveR σ).Contains (at' σ (oSave+80+8*i)) 8 :=
      Offset.contains (scr σ) (d := oSave+80+8*i) (e := oSave) (n := 8) (k := 144)
        (by omega) (by omega) (by decide)
    rw [hf.readW hc hsave (by decide)]
    exact he.savedV i hi

theorem Env.lowStep {σ s t : State} (he : Env σ s) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hsub : ∀ r ∈ rs,Region.Sub r (lowR σ))
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ [Reg.x19,.x20,.x21,.x30],t.gpr r = s.gpr r) : Env σ t :=
  he.frameStep hf (fun r hm => ⟨scrR σ,by simp,fun x hx =>
      (Region.sub_prefix (by decide : oSave ≤ 8192)) x (hsub r hm x hx)⟩)
    (fun r hm => (low_save σ).sub_right (hsub r hm)) hr hw hsp hg
end VG.Proof.MlDsa.AArch64.Sample.Rej4
