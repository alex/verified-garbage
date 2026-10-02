import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SqAdvance

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (count_loop)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (squeezeStepWith)

theorem squeezeStep_ok (sha3 : Bool) {σ s : State} (hp : Pre σ) {n : Nat} (hn : n < 6) (h : Phase σ n 0 s) :
    WP isa (squeezeStepWith sha3) s (Phase σ (n+1) 0) := by
  unfold squeezeStepWith
  refine WP.seq (WP.mono (phasePair_ok sha3 hp hn (by decide : 0 < 2) h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (phasePair_ok sha3 hp hn (by decide : 1 < 2) h1) fun s2 h2 => ?_)
  exact phaseAdvance_ok hn h2

theorem squeeze_ok (sha3 : Bool) {σ s : State} (hp : Pre σ) (h : Phase σ 0 0 s) :
    WP isa (.loop (squeezeStepWith sha3) (.nonzero .x .x28)) s (Phase σ 6 0) := by
  refine count_loop (by decide : 0 < 6) (fun n t => Phase σ n 0 t) (fun n hn t ht => ?_) h
  refine WP.mono (squeezeStep_ok sha3 hp hn ht) fun u hu => ⟨hu,?_⟩
  rw [hu.count]
  omega
end VG.Proof.MlDsa.AArch64.Sample.Rej4
