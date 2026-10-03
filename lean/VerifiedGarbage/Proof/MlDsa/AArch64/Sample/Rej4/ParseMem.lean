import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Sponge

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlDsa.Sample (polyR coeffAddr)

def polyP (σ : State) (k : Nat) : Addr := aP σ+BitVec.ofNat 64 (1024*k)

theorem poly_sub (σ : State) {k : Nat} (hk : k < 4) : Region.Sub (polyR (polyP σ k)) (aR σ) :=
  Offset.sub_base (aP σ) (by omega)

theorem buf_sub (σ : State) {k : Nat} (hk : k < 4) : Region.Sub (⟨bufP σ k,1008⟩ : Region) (scrR σ) :=
  Offset.sub_base (scr σ) (by dsimp only [VG.Impl.MlDsa.AArch64.Sample.Rej4.oBuf]; omega)

theorem buf_poly {σ : State} (hp : Pre σ) {j k : Nat} (hj : j < 4) (hk : k < 4) :
    (⟨bufP σ j,1008⟩ : Region).Disjoint (polyR (polyP σ k)) :=
  hp.a_scr.symm.sub_left (buf_sub σ hj) |>.sub_right (poly_sub σ hk)

theorem coeffs_in {σ s : State} (hp : Pre σ) (hw : s.wr = σ.wr) {k : Nat} (hk : k < 4) :
    ∀ i < 256,InRegions s.wr (coeffAddr (polyP σ k) i) 4 := by
  intro i hi
  rw [hw,hp.wr]
  refine ⟨aR σ,by simp,?_⟩
  unfold coeffAddr polyP
  rw [Offset.add_add]
  exact Offset.contains_base _ (by omega) (by omega)

theorem Env.polyStep {σ s t : State} (hp : Pre σ) {k : Nat} (hk : k < 4) (he : Env σ s)
    (hf : Frame [polyR (polyP σ k)] s.mem t.mem)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ [Reg.x19,.x20,.x21,.x30],t.gpr r = s.gpr r) : Env σ t :=
  he.frameStep hf (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨aR σ,by simp,poly_sub σ hk⟩)
    (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.a_scr.symm.sub_left (Offset.sub_base (scr σ) (by decide)) |>.sub_right (poly_sub σ hk))
    hr hw hsp hg

theorem Ready.polyStep {σ s t : State} (hp : Pre σ) {k : Nat} (hk : k < 4) (h : Ready σ s)
    (hf : Frame [polyR (polyP σ k)] s.mem t.mem)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hg : ∀ r ∈ [Reg.x19,.x20,.x21,.x30],t.gpr r = s.gpr r) : Ready σ t := by
  refine ⟨h.env.polyStep hp hk hf hr hw hsp hg,fun j hj i hi => ?_⟩
  rw [← h.out j hj i hi]
  exact hf _ (fun r hr hc => by
    rw [List.mem_singleton.mp hr] at hc
    exact buf_poly hp hj hk _ (Offset.contains_base _ (by omega) (by omega)) hc)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
