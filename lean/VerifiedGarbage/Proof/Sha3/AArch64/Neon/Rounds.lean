import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.Vector
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

/-- All 24 rounds of Keccak-f[1600] on two independent NEON states. -/
theorem rounds_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) :
    WP isa (.block rounds) s fun s' => CoreKeep s s' ∧ Pairs s' (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) := by
  unfold rounds
  refine wp_range_flatMap (M := isa)
    (fun k s' => CoreKeep s s' ∧ Pairs s'
      ((List.range k).foldl Spec.Sha3.rnd A) ((List.range k).foldl Spec.Sha3.rnd B))
    (fun k s' hk ⟨hc,hp'⟩ => ?_) 24 (Nat.le_refl _) s ⟨CoreKeep.refl _,hp⟩
  refine WP.mono (round_ok hp' hk) fun s'' ⟨hc',hp''⟩ => ⟨hc.trans hc',?_⟩
  simpa only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil] using hp''
end VG.Proof.Sha3.AArch64.Neon
