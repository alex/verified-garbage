import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbArgs
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (absorbPair oSave)

theorem pair_sub {σ : State} {p : Nat} (hp : p < 2) : Region.Sub (pairR (stateP σ p)) (lowR σ) :=
  Offset.sub_base (scr σ) (by dsimp only [oSave]; omega)

theorem absorbPair_ok {σ s : State} (hp : Pre σ) (he : Env σ s) {p : Nat} (hpn : p < 2)
    (hz : ∀ i < 25,s.mem.read (wordAddr (stateP σ p) i) 16 = 0) :
    WP isa (.block (absorbPair p)) s fun t => Env σ t ∧
      PairAt t.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1)) ∧
      Frame [pairR (stateP σ p)] s.mem t.mem := by
  unfold absorbPair
  rw [WP.block_append_iff]
  refine WP.mono (absorbArgs_ok hpn) fun s1 ⟨h1,e2,e3,e4⟩ => ?_
  have he1 : Env σ s1 := he.lowStep (rs := []) (by rw [h1.mem]; exact Frame.refl _ _)
    (by simp) h1.rd h1.wr h1.sp (fun r hr => h1.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  let a := seedP σ+BitVec.ofNat 64 (34*(2*p))
  let b := seedP σ+BitVec.ofNat 64 (34*(2*p+1))
  have e2' : s1.gpr .x2 = stateP σ p := by rw [e2,he.x19]; rfl
  have e3' : s1.gpr .x3 = a := by rw [e3,he.x20,show 68*p = 34*(2*p) by omega]
  have e4' : s1.gpr .x4 = b := by rw [e4,he.x20,show 68*p+34 = 34*(2*p+1) by omega]
  have seed_in (k : Nat) (hk : k < 4) (d n : Nat) (hd : d+n ≤ 34) :
      InRegions (s1.rd++s1.wr) ((seedP σ+BitVec.ofNat 64 (34*k))+BitVec.ofNat 64 d) n := by
    rw [Offset.add_add]
    exact in_seed hp he1.rd (by omega)
  have hws : ∀ j < 25,InRegions s1.wr (wordAddr (stateP σ p) j) 16 := by
    intro j hj
    unfold wordAddr stateP at'
    rw [Offset.add_add]
    exact in_scr hp he1.wr (by omega)
  have hps : Region.Sub (pairR (stateP σ p)) (scrR σ) :=
    Offset.sub_base (scr σ) (by omega)
  refine WP.mono (absorbBody_ok e2' e3' e4'
    (fun j hj => seed_in (2*p) (by omega) (8*j) 8 (by omega))
    (fun j hj => seed_in (2*p+1) (by omega) (8*j) 8 (by omega))
    (seed_in (2*p) (by omega) 32 1 (by decide)) (seed_in (2*p) (by omega) 33 1 (by decide))
    (seed_in (2*p+1) (by omega) 32 1 (by decide)) (seed_in (2*p+1) (by omega) 33 1 (by decide))
    hws ((hp.seed_scr.sub_left (seed_sub (by omega))).sub_right hps)
    ((hp.seed_scr.sub_left (seed_sub (by omega))).sub_right hps)
    (by intro i hi; rw [h1.mem]; exact hz i hi)) fun t ⟨h2,hf2,hp2⟩ => ?_
  refine ⟨he1.lowStep hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact pair_sub hpn)
    h2.rd h2.wr h2.sp (fun r hr => h2.gpr r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),?_,?_⟩
  · rw [seedState_eq,seedState_eq,seed_eq hp he1 (by omega : 2*p < 4),seed_eq hp he1 (by omega : 2*p+1 < 4)] at hp2
    exact hp2
  · rw [← h1.mem]; exact hf2
end VG.Proof.MlDsa.AArch64.Sample.Rej4
