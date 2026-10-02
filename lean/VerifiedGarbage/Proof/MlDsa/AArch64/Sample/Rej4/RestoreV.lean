import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Sponge

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (restoreV oSave)

theorem low_setLane (v : BitVec 128) (a : BitVec 64) : vdword (setLane v 64 0 a) 0 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword,setLane,BitVec.getLsbD_extractLsb',BitVec.getLsbD_or,
    BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth,BitVec.getLsbD_allOnes]
  simp (disch := omega) [hi,decide_eq_true]

theorem restoreV_step {s : State} {p : Addr} {i : Nat} (hi : i < 8) (hp : s.gpr .x19 = p)
    (hin : InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (oSave+80+8*i)) 8) :
    WP isa (.block ([.ldr .x .x8 .x19 (oSave+80+8*i),.vop (.ins .d2 (vreg (8+i)) 0 .x8)] : List Instr)) s
      fun t => RegKeep [.x8] s t ∧ t.mem = s.mem ∧
        vdword (t.v (vreg (8+i))) 0 = s.mem.readW (p+BitVec.ofNat 64 (oSave+80+8*i)) 64 ∧
        ∀ r, r ≠ vreg (8+i) → t.v r = s.v r := by
  refine wp_ldr ⟨by dsimp only [oSave]; omega,by dsimp only [oSave]; omega⟩
    (by rw [hp]) hin fun u h1 => ?_
  refine wp_vop (d := vreg (8+i)) rfl fun t h2 => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact ((RegKeep.upd h1).trans (RegKeep.vupd h2)).mono (by simp)
  · exact h2.mem.trans h1.mem
  · rw [h2.v,low_setLane,h1.gpr]
  · intro r hr
    rw [h2.other r hr,h1.vec]

theorem restoreV_ok {σ s : State} (hp : Pre σ) (he : Env σ s) :
    WP isa (.block restoreV) s fun t => RegKeep [.x8] s t ∧ t.mem = s.mem ∧
      ∀ i < 8,vdword (t.v (vreg (8+i))) 0 = vdword (σ.v (vreg (8+i))) 0 := by
  unfold restoreV
  refine wp_range_flatMap (M := isa)
    (fun k t => RegKeep [.x8] s t ∧ t.mem = s.mem ∧
      ∀ i < k,vdword (t.v (vreg (8+i))) 0 = vdword (σ.v (vreg (8+i))) 0)
    (fun k t hk ⟨ht,hm,hvals⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine WP.mono (restoreV_step hk ((ht.gpr .x19 (by decide)).trans he.x19)
    (in_scr_rd hp (ht.rd.trans he.rd) (ht.wr.trans he.wr) (by dsimp only [oSave]; omega)))
      fun u ⟨hu,hmu,hvu,hother⟩ => ?_
  refine ⟨(ht.trans hu).mono (by simp),hmu.trans hm,fun i hi => ?_⟩
  by_cases heq : i = k
  · subst i
    rw [hvu,hm]
    exact he.savedV k hk
  · rw [hother (vreg (8+i)) (fun h => heq (by
      have e := (vreg_inj (8+i) (by omega) (8+k) (by omega)).mp h
      omega))]
    exact hvals i (by omega)
end VG.Proof.MlDsa.AArch64.Sample.Rej4
