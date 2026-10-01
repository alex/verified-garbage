import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.BoundaryCommon

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (laneAddr lane_contains lane_sep)

theorem zip1_pair (a b : BitVec 128) :
    VPermOp.eval .zip1 .d2 a b = ofVDwords (vdword a 0) (vdword b 0) := by
  simp [VPermOp.eval,VArr.lanes,VArr.ofLanes]

structure StoreKeep (s s' : VG.AArch64.State) : Prop where
  ptr : Ptrs s s'
  lanes : ∀ j < 25, low s' (vreg j) = low s (vreg j)

theorem StoreKeep.refl (s : VG.AArch64.State) : StoreKeep s s := ⟨Ptrs.refl _,fun _ _ => rfl⟩
theorem StoreKeep.trans {s t u : VG.AArch64.State} (h : StoreKeep s t) (k : StoreKeep t u) : StoreKeep s u :=
  ⟨h.ptr.trans k.ptr,fun j hj => (k.lanes j hj).trans (h.lanes j hj)⟩

theorem storePair_ok (s : VG.AArch64.State) (i : Nat) (hi : i < 12)
    (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (storePair i)) s fun s' => StoreKeep s s' ∧
      s'.mem = s.mem.write (s.gpr .x0 + BitVec.ofNat 64 (16*i)) 16
        (ofVDwords (low s (vreg (2*i))) (low s (vreg (2*i+1)))) := by
  unfold storePair
  refine WP.cons (s' := s.setV .v25 (ofVDwords (low s (vreg (2*i))) (low s (vreg (2*i+1)))))
    ?_ (WP.cons (exec_strq ⟨by omega,by omega⟩ hout) (wp_nil ?_))
  · simp only [exec_vop,VOp.eval,zip1_pair,Option.map_some,low]
  · refine ⟨⟨⟨rfl,rfl,rfl,rfl,rfl⟩,fun j hj => ?_⟩,?_⟩
    · change low (s.setV .v25 _) (vreg j) = _
      rw [low_setV]
      have hn : vreg j ≠ .v25 := (show ∀ j < 25, vreg j ≠ .v25 by decide) j hj
      simp only [put,hn,ite_false]
    · simp only [RegUpd.gpr_setV,RegUpd.mem_setV,RegUpd.v_setV_self]

structure StoreInv (s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : StoreKeep s₀ s
  frame : Frame [⟨s₀.gpr .x0,200⟩] s₀.mem s.mem
  vals : ∀ j < 2*k, s.mem.readW (laneAddr (s₀.gpr .x0) j) 64 = low s₀ (vreg j)

theorem storePairs_ok (s₀ : VG.AArch64.State)
    (hout : ∀ i < 12, InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range 12).flatMap storePair)) s₀ (StoreInv s₀ 12) := by
  refine wp_range_flatMap (M := isa) (StoreInv s₀) (fun i s hi hs => ?_)
    12 (Nat.le_refl _) s₀ ⟨StoreKeep.refl _,Frame.refl _ _,fun _ h => absurd h (by omega)⟩
  refine (storePair_ok s i hi (by rw [hs.keep.ptr.wr,hs.keep.ptr.x0]; exact hout i hi)).mono
    fun s' ⟨hk,hm⟩ => ⟨hs.keep.trans hk,?_,fun j hj => ?_⟩
  · rw [hm,hs.keep.ptr.x0]
    exact hs.frame.write (by simp) _ (state_pair_contains s₀ hi)
  · rw [hm,hs.keep.ptr.x0,write16_dwords]
    have he : s₀.gpr .x0 + BitVec.ofNat 64 (16*i) = laneAddr (s₀.gpr .x0) (2*i) := by
      simp only [laneAddr,show 8*(2*i)=16*i by omega]
    have ho : s₀.gpr .x0 + BitVec.ofNat 64 (16*i) + BitVec.ofNat 64 8 = laneAddr (s₀.gpr .x0) (2*i+1) := by
      simp only [laneAddr,BitVec.add_assoc,← BitVec.ofNat_add,show 16*i+8=8*(2*i+1) by omega]
    rw [ho,he]
    by_cases hodd : j = 2*i+1
    · subst j
      rw [Mem.readW_writeW_self64,hs.keep.lanes _ (by omega)]
    · rw [Mem.readW_writeW_sep (lane_sep _ (by omega) (by omega) hodd) (by decide)]
      by_cases heven : j = 2*i
      · subst j
        rw [Mem.readW_writeW_self64,hs.keep.lanes _ (by omega)]
      · rw [Mem.readW_writeW_sep (lane_sep _ (by omega) (by omega) heven) (by decide)]
        exact hs.vals j (by omega)

theorem store_ok (s₀ : VG.AArch64.State) (A : Spec.Sha3.State) (hA : Lanes s₀ A)
    (hout : ∀ i < 12, InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 (16*i)) 16)
    (hlast : InRegions s₀.wr (laneAddr (s₀.gpr .x0) 24) 8) :
    WP isa (.block store) s₀ fun s' => Ptrs s₀ s' ∧
      Frame [⟨s₀.gpr .x0,200⟩] s₀.mem s'.mem ∧ Spec.Sha3.stateAt s'.mem (s₀.gpr .x0) = A := by
  rw [store,WP.block_append_iff]
  refine (storePairs_ok s₀ hout).mono fun s hs => ?_
  unfold storeLast
  refine WP.cons (exec_umov_low s .x17 .v24) (WP.cons (exec_str_x (by decide) ?_) (wp_nil ?_))
  · simpa (config := {decide := true}) only [RegUpd.gpr_write,RegUpd.wr_write,ite_false,
      hs.keep.ptr.wr,hs.keep.ptr.x0] using hlast
  · refine ⟨?_,?_,?_⟩
    · constructor <;> simp (config := {decide := true}) only [RegUpd.gpr_write,ite_false,
        RegUpd.rd_write,RegUpd.wr_write,RegUpd.sp_write,
        hs.keep.ptr.x0,hs.keep.ptr.x1,hs.keep.ptr.rd,hs.keep.ptr.wr,hs.keep.ptr.sp]
    · change Frame _ _ ((s.write .x .x17 _).mem.writeW _ ((s.write .x .x17 _).gpr .x17))
      simp (config := {decide := true}) only [RegUpd.mem_write,RegUpd.gpr_write,ite_true,ite_false,
        Size.bits,BitVec.setWidth_eq,hs.keep.ptr.x0]
      change Frame [⟨s₀.gpr .x0,200⟩] s₀.mem
        (s.mem.writeW (laneAddr (s₀.gpr .x0) 24) (low s (vreg 24)))
      exact hs.frame.writeW (r := ⟨s₀.gpr .x0,200⟩) (by simp) (low s (vreg 24))
        (lane_contains (s₀.gpr .x0) (by decide : 24 < 25))
    · apply Vector.ext
      intro j hj
      simp (config := {decide := true}) only [Spec.Sha3.stateAt,Vector.getElem_ofFn,
        RegUpd.mem_write,RegUpd.gpr_write,ite_true,ite_false,Size.bits,BitVec.setWidth_eq,hs.keep.ptr.x0]
      change (s.mem.writeW (laneAddr (s₀.gpr .x0) 24) (low s (vreg 24))).readW _ 64 = A[j]
      by_cases he : j = 24
      · subst j
        rw [Mem.readW_writeW_self64,hs.keep.lanes 24 (by decide)]
        exact hA 24 (by decide)
      · rw [Mem.readW_writeW_sep (lane_sep _ hj (by decide) he) (by decide),hs.vals j (by omega)]
        exact hA j hj

end VG.Proof.Sha3.AArch64.Sha3.Vector
