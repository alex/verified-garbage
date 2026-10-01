import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure SaveInv (orig : State) (k : Nat) (s : State) : Prop where
  keep : Keep orig s
  gpr : s.gpr = orig.gpr
  mem : s.mem = orig.mem
  vals : ∀ i < k, vdword (s.v (savedVec i)) 0 = orig.gpr (savedReg i)
  vec : ∀ r ∈ preservedV, s.v r = orig.v r

theorem save_vectors_ok (orig : State) :
    WP isa (.block ((List.range 11).map fun i => .vop (.dup .d2 (savedVec i) (savedReg i))))
      orig (SaveInv orig 11) := by
  rw [show (List.range 11).map (fun i => Instr.vop (.dup .d2 (savedVec i) (savedReg i))) =
    (List.range 11).flatMap (fun i => [Instr.vop (.dup .d2 (savedVec i) (savedReg i))]) by rfl]
  refine wp_range_flatMap (M := isa) (SaveInv orig) (fun i s hi hs => ?_)
    11 (Nat.le_refl _) orig ⟨Keep.refl _,rfl,rfl,fun _ h => by omega,fun _ _ => rfl⟩
  refine WP.cons rfl (wp_nil ?_)
  refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.gpr,hs.mem,fun j hj => ?_,fun r hr => ?_⟩
  · simp only [RegUpd.v_setV,savedVec_inj j (by omega) i hi]
    split
    · rename_i h; subst j
      simp only [vdword_ofVDwords_0,hs.gpr]
    · exact hs.vals j (by omega)
  · simp only [RegUpd.v_setV,savedVec_not_preserved i hi r hr,ite_false]
    exact hs.vec r hr

theorem save_ok (orig : State) (_hp : VG.Proof.Sha3.AArch64.Pre orig) :
    WP isa (.block save) orig fun s => Keep orig s ∧ s.gpr = orig.gpr ∧
      s.mem = orig.mem ∧ SavedVector orig s ∧ Ptrs orig s ∧
      (∀ r ∈ preservedV, s.v r = orig.v r) := by
  unfold save
  rw [WP.block_append_iff]
  refine (save_vectors_ok orig).mono fun s hs => ?_
  refine WP.cons rfl (WP.cons rfl (wp_nil ?_))
  refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.gpr,hs.mem,?_,?_,?_⟩
  · intro i hi
    have hn := savedVec_ne_ptrs i hi
    simp only [RegUpd.v_setV,hn.1,hn.2,ite_false]
    exact hs.vals i hi
  · simp only [Ptrs,RegUpd.v_setV,reduceCtorEq,ite_false,ite_true,
      vdword_ofVDwords_0,RegUpd.gpr_setV,hs.gpr]
    exact ⟨True.intro,True.intro⟩
  · intro r hr
    have hn : ∀ r ∈ preservedV, r ≠ .v30 ∧ r ≠ .v31 := by decide
    simp only [RegUpd.v_setV,(hn r hr).1,(hn r hr).2,ite_false]
    exact hs.vec r hr
end VG.Proof.Sha3.AArch64.Scalar.Boundary
