import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRound

namespace VG.Proof.Sha3.AArch64.Neon.Hw
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

theorem rounds2_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) :
    WP isa (.block rounds) s fun t => CoreKeep s t ∧ Pairs t (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) := by
  unfold rounds
  refine wp_range_flatMap (M := isa)
    (fun k t => CoreKeep s t ∧ Pairs t
      ((List.range k).foldl Spec.Sha3.rnd A) ((List.range k).foldl Spec.Sha3.rnd B))
    (fun k t hk ⟨ht,hpt⟩ => ?_) 24 (Nat.le_refl _) s ⟨CoreKeep.refl _,hp⟩
  refine WP.mono (round2_ok hpt hk) fun u ⟨hu,hpu⟩ => ⟨ht.trans hu,?_⟩
  simpa only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil] using hpu
end VG.Proof.Sha3.AArch64.Neon.Hw
