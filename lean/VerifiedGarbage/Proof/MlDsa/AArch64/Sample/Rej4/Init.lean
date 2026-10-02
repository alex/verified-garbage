import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (init)

theorem pairs_disjoint (σ : State) : (pairR (stateP σ 0)).Disjoint (pairR (stateP σ 1)) :=
  Offset.disjoint (scr σ) (d := 400*0) (e := 400*1) (n := 400) (k := 400) (by decide) (by decide) (by decide)

theorem state_word (σ : State) (p i : Nat) : wordAddr (stateP σ p) i = wordAddr (scr σ) (25*p+i) := by
  unfold wordAddr stateP at'
  rw [Offset.add_add,show 400*p+16*i = 16*(25*p+i) by omega]

/-- Absorb all four seeds as two pairs of lanes, preserving the ABI save record. -/
theorem init_ok {σ : State} (hp : Pre σ) : WP isa (.block init) σ fun t => Env σ t ∧
    PairAt t.mem (stateP σ 0) (A0 σ 0) (A0 σ 1) ∧
    PairAt t.mem (stateP σ 1) (A0 σ 2) (A0 σ 3) := by
  unfold init
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (pro_ok hp) fun s1 he1 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zeroAll_ok hp he1) fun s2 ⟨he2,hz2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (absorbPair_ok (p := 0) hp he2 (by decide : 0 < 2) (fun i hi => by
    rw [state_word,Nat.mul_zero,Nat.zero_add]; exact hz2 i (by omega))) fun s3 ⟨he3,hp3,hf3⟩ => ?_
  have hz3 : ∀ i < 25,s3.mem.read (wordAddr (stateP σ 1) i) 16 = 0 := by
    intro i hi
    rw [hf3.read (pair_contains (stateP σ 1) hi) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (pairs_disjoint σ).symm) (by decide),state_word]
    exact hz2 (25+i) (by omega)
  refine WP.mono (absorbPair_ok (p := 1) hp he3 (by decide : 1 < 2) hz3) fun t ⟨het,hpt,hft⟩ => ?_
  refine ⟨het,?_,hpt⟩
  intro i hi
  rw [hft.read (pair_contains (stateP σ 0) hi) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact pairs_disjoint σ) (by decide)]
  exact hp3 i hi
end VG.Proof.MlDsa.AArch64.Sample.Rej4
