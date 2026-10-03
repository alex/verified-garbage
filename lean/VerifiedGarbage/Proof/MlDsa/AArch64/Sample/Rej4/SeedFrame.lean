import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Base

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64

theorem seed_sub {σ : State} {k : Nat} (hk : k < 4) :
    Region.Sub (seedR (seedP σ+BitVec.ofNat 64 (34*k))) (seedsR σ) :=
  Offset.sub_base (seedP σ) (by omega)

theorem seed_eq {σ s : State} (hp : Pre σ) (he : Env σ s) {k : Nat} (hk : k < 4) :
    Spec.Sha3.bytesAt s.mem (seedP σ+BitVec.ofNat 64 (34*k)) 34 = B σ k := by
  refine Proof.MlKem.bytesAt_frame he.frame ?_ (by decide)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.seed_a.sub_left (seed_sub hk)
  · exact hp.seed_scr.sub_left (seed_sub hk)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
