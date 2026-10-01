import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure SaveInv (s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : Keep s₀ s
  gpr : s.gpr = s₀.gpr
  vec : s.v = s₀.v
  frame : Frame [⟨s₀.gpr .x1,512⟩] s₀.mem s.mem
  vals : ∀ i < k, s.mem.readW (s₀.gpr .x1 + BitVec.ofNat 64 (8*i)) 64 = s₀.gpr (savedReg i)

theorem save_stores_ok (s₀ : VG.AArch64.State) (hp : VG.Proof.Sha3.AArch64.Pre s₀) :
    WP isa (.block ((List.range 11).map fun i => .str .x (savedReg i) .x1 (8*i)))
      s₀ (SaveInv s₀ 11) := by
  have hm : (List.range 11).map (fun i => Instr.str .x (savedReg i) .x1 (8*i)) =
      (List.range 11).flatMap (fun i => [Instr.str .x (savedReg i) .x1 (8*i)]) := by
    rfl
  rw [hm]
  refine wp_range_flatMap (M := isa) (SaveInv s₀) (fun i s hi hs => ?_)
    11 (Nat.le_refl _) s₀ ⟨Keep.refl _,rfl,rfl,Frame.refl _ _,fun _ h => absurd h (by omega)⟩
  refine WP.cons (exec_str_x ⟨by omega,by omega⟩ ?_) (wp_nil ?_)
  · rw [hs.keep.wr,hs.gpr]
    exact hp.in_wr (.inr rfl) (scratch_contains s₀ hi)
  · refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.gpr,hs.vec,?_,fun j hj => ?_⟩
    · change Frame _ _ (s.mem.writeW _ _)
      rw [hs.gpr]
      exact hs.frame.writeW (by simp) _ (scratch_contains s₀ hi)
    · change (s.mem.writeW _ _).readW _ 64 = _
      rw [hs.gpr]
      by_cases he : j = i
      · subst j
        exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact hs.vals j (by omega)

theorem save_ok (s₀ : VG.AArch64.State) (hp : VG.Proof.Sha3.AArch64.Pre s₀) :
    WP isa (.block save) s₀ fun s' => Keep s₀ s' ∧ s'.gpr = s₀.gpr ∧
      Frame [⟨s₀.gpr .x1,512⟩] s₀.mem s'.mem ∧ Saved s₀ s'.mem ∧ Ptrs s₀ s' ∧
      (∀ r, r ≠ .v30 → r ≠ .v31 → s'.v r = s₀.v r) := by
  unfold save
  rw [WP.block_append_iff]
  refine (save_stores_ok s₀ hp).mono fun s hs => ?_
  refine WP.cons rfl (WP.cons rfl (wp_nil ?_))
  refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.gpr,hs.frame,hs.vals,?_,?_⟩
  · simp only [Ptrs,RegUpd.v_setV,reduceCtorEq,ite_false,ite_true,vdword_ofVDwords_0,RegUpd.gpr_setV,hs.gpr]
    exact ⟨True.intro,True.intro⟩
  · intro r h30 h31
    simp only [RegUpd.v_setV,h30,h31,ite_false,hs.vec]

end VG.Proof.Sha3.AArch64.Scalar.Boundary
