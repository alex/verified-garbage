import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.BoundaryCommon

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (laneAddr)

theorem pair_low (m : Mem) (p : Addr) (i : Nat) :
    vdword (m.read (p + BitVec.ofNat 64 (16*i)) 16) 0 = m.readW (laneAddr p (2*i)) 64 := by
  rw [vdword_read16 _ _ (by decide)]
  simp only [laneAddr,Nat.mul_zero,BitVec.add_zero,show 8*(2*i)=16*i by omega]

theorem pair_high (m : Mem) (p : Addr) (i : Nat) :
    vdword (m.read (p + BitVec.ofNat 64 (16*i)) 16) 1 = m.readW (laneAddr p (2*i+1)) 64 := by
  rw [vdword_read16 _ _ (by decide)]
  simp only [laneAddr,Nat.mul_one,BitVec.add_assoc,← BitVec.ofNat_add,
    show 16*i+8=8*(2*i+1) by omega]

theorem loadPair_ok (s : VG.AArch64.State) (i : Nat) (hi : i < 12)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (loadPair i)) s fun s' => Keep s s' ∧ ∀ j < 25,
      low s' (vreg j) = if j = 2*i+1 then s.mem.readW (laneAddr (s.gpr .x0) (2*i+1)) 64
        else if j = 2*i then s.mem.readW (laneAddr (s.gpr .x0) (2*i)) 64 else low s (vreg j) := by
  unfold loadPair
  let q := s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (16*i)) 16
  refine WP.cons (exec_ldrq ⟨by omega,by omega⟩ hin) (WP.cons
    (s' := (s.setV (vreg (2*i)) q).setV (vreg (2*i+1)) (((q ++ q) >>> (8*8)).extractLsb' 0 128))
    ?_ (wp_nil ?_))
  · simp only [exec_vop,VOp.eval,show 8 < 16 by decide,ite_true,Option.map_some,RegUpd.v_setV_self,q]
  · refine ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,fun j hj => ?_⟩
    rw [low_setV]
    simp only [put]
    rw [low_setV]
    simp only [put,vreg_inj j (by omega) (2*i+1) (by omega),
      vreg_inj j (by omega) (2*i) (by omega),q,pair_low]
    rw [low_ext8, pair_high]

structure LoadInv (s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : Keep s₀ s
  lanes : ∀ j < 2*k, low s (vreg j) = s₀.mem.readW (laneAddr (s₀.gpr .x0) j) 64

theorem load_ok (s₀ : VG.AArch64.State)
    (hp : ∀ i < 12, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 (16*i)) 16)
    (hl : InRegions (s₀.rd ++ s₀.wr) (laneAddr (s₀.gpr .x0) 24) 8) :
    WP isa (.block load) s₀ fun s' => Ptrs s₀ s' ∧ s'.mem = s₀.mem ∧
      Lanes s' (Spec.Sha3.stateAt s₀.mem (s₀.gpr .x0)) := by
  have hh : WP isa (.block ((List.range 12).flatMap loadPair)) s₀ (LoadInv s₀ 12) := by
    refine wp_range_flatMap (M := isa) (LoadInv s₀) (fun i s hi hs => ?_)
      12 (Nat.le_refl _) s₀ ⟨Keep.refl _,fun _ h => absurd h (by omega)⟩
    refine (loadPair_ok s i hi (by rw [hs.keep.rd,hs.keep.wr,hs.keep.gpr]; exact hp i hi)).mono
      fun s' ⟨hk,ha⟩ => ⟨hs.keep.trans hk,fun j hj => ?_⟩
    rw [ha j (by omega)]
    split
    · rename_i he; subst j
      rw [hs.keep.mem,hs.keep.gpr]
    · split
      · rename_i he; subst j
        rw [hs.keep.mem,hs.keep.gpr]
      · exact hs.lanes j (by omega)
  rw [load,WP.block_append_iff]
  refine hh.mono fun s hs => ?_
  unfold loadLast
  refine WP.cons (exec_ldr_x (by decide) ?_) (WP.cons rfl (wp_nil ?_))
  · rw [hs.keep.rd,hs.keep.wr,hs.keep.gpr]
    exact hl
  · refine ⟨?_,hs.keep.mem,fun j hj => ?_⟩
    · constructor <;> simp (config := {decide := true}) only [RegUpd.gpr_setV,RegUpd.gpr_write,
        ite_false,RegUpd.rd_setV,RegUpd.rd_write,RegUpd.wr_setV,RegUpd.wr_write,
        RegUpd.sp_setV,RegUpd.sp_write,hs.keep.gpr,hs.keep.rd,hs.keep.wr,hs.keep.sp]
    · simp only [Spec.Sha3.stateAt,Vector.getElem_ofFn,low,RegUpd.v_setV,
        RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq]
      have he : vreg j = .v24 ↔ j = 24 := vreg_inj j (by omega) 24 (by decide)
      simp only [he]
      split
      · rename_i he; subst j
        rw [vdword_ofVDwords_0,hs.keep.mem,hs.keep.gpr]
      · exact hs.lanes j (by omega)

end VG.Proof.Sha3.AArch64.Sha3.Vector
