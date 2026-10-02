import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Setup
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Squeeze

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (init setup squeezeStepWith)

structure Ready (σ s : State) : Prop where
  env : Env σ s
  out : ∀ k < 4, ∀ j < 1008, s.mem (bufP σ k+BitVec.ofNat 64 j) = F σ k j

theorem sponge_ok (sha3 : Bool) {σ : State} (hp : Pre σ) :
    WP isa (.seq (.block (init++setup))
      (.loop (squeezeStepWith sha3) (.nonzero .x .x28))) σ (Ready σ) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (init_ok hp) fun s ⟨he,h0,h1⟩ => ?_
  refine WP.mono (setup_ok he h0 h1) fun u hu => ?_
  refine WP.mono (squeeze_ok sha3 hp hu) fun t ht => ⟨ht.env,?_⟩
  intro k hk j hj
  exact ht.out k hk j (by simpa using hj)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
