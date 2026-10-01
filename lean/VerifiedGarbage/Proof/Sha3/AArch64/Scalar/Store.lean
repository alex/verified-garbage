import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure StoreInv (s₀ : VG.AArch64.State) (p : Addr) (A : Spec.Sha3.State)
    (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : Keep s₀ s
  gpr : s.gpr = s₀.gpr
  vec : s.v = s₀.v
  frame : Frame [⟨p,200⟩] s₀.mem s.mem
  vals : ∀ i (_hi : i < k) (h25 : i < 25), s.mem.readW (p + BitVec.ofNat 64 (8*i)) 64 = A[i]

theorem store_words_ok (s₀ : VG.AArch64.State) (A : Spec.Sha3.State)
    (hA : Lanes s₀ A)
    (hin : ∀ i < 25, InRegions s₀.wr (s₀.gpr .x30 + BitVec.ofNat 64 (8*i)) 8) :
    WP isa (.block ((List.range 25).map fun i => .str .x (laneReg i) .x30 (8*i)))
      s₀ (StoreInv s₀ (s₀.gpr .x30) A 25) := by
  rw [show (List.range 25).map (fun i => Instr.str .x (laneReg i) .x30 (8*i)) =
    (List.range 25).flatMap (fun i => [Instr.str .x (laneReg i) .x30 (8*i)]) by rfl]
  refine wp_range_flatMap (M := isa) (StoreInv s₀ (s₀.gpr .x30) A) (fun i s hi hs => ?_)
    25 (Nat.le_refl _) s₀ ⟨Keep.refl _,rfl,rfl,Frame.refl _ _,fun _ h => absurd h (by omega)⟩
  refine WP.cons (exec_str_x ⟨by omega,by omega⟩ ?_) (wp_nil ?_)
  · rw [hs.keep.wr,hs.gpr]
    exact hin i hi
  · refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.gpr,hs.vec,?_,fun j hj h25 => ?_⟩
    · change Frame _ _ (s.mem.writeW _ _)
      rw [hs.gpr]
      exact hs.frame.writeW (r := ⟨s₀.gpr .x30,200⟩) (by simp) _ (Offset.contains_base _ (by omega) (by omega))
    · change (s.mem.writeW _ _).readW _ 64 = _
      rw [hs.gpr]
      by_cases he : j = i
      · subst j
        rw [Mem.readW_writeW_self64]
        exact hA i hi
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact hs.vals j (by omega) h25

theorem store_ok (s₀ : VG.AArch64.State) (p : Addr) (A : Spec.Sha3.State)
    (hA : Lanes s₀ A) (hptr : vdword (s₀.v .v30) 0 = p)
    (hin : ∀ i < 25, InRegions s₀.wr (p + BitVec.ofNat 64 (8*i)) 8) :
    WP isa (.block store) s₀ fun s' => Keep s₀ s' ∧ s'.v = s₀.v ∧
      Frame [⟨p,200⟩] s₀.mem s'.mem ∧ Spec.Sha3.stateAt s'.mem p = A := by
  change (s₀.v .v30).extractLsb' (64*0) 64 = p at hptr
  unfold store
  refine WP.cons rfl ?_
  refine (store_words_ok _ A ?_ ?_).mono fun s hs => ?_
  · intro i hi
    simpa only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,laneReg_ne_x30 i hi,ite_false]
      using hA i hi
  · intro i hi
    simpa only [RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq,RegUpd.wr_write,hptr] using hin i hi
  · have hb : (s₀.write .x .x30 ((s₀.v .v30).extractLsb' (64*0) 64)).gpr .x30 = p := by
      simpa only [RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq,vdword] using hptr
    refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.vec,?_,?_⟩
    · simpa only [hb,RegUpd.mem_write] using hs.frame
    · apply Vector.ext
      intro i hi
      simpa only [Spec.Sha3.stateAt,Vector.getElem_ofFn,VG.Proof.Sha3.laneAddr,hb]
        using hs.vals i hi hi

end VG.Proof.Sha3.AArch64.Scalar.Boundary
