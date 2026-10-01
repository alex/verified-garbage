import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure LoadInv (s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : Keep s₀ s
  mem : s.mem = s₀.mem
  vec : s.v = s₀.v
  base : s.gpr .x30 = s₀.gpr .x0
  lanes : ∀ j < k, s.gpr (laneReg j) =
    s₀.mem.readW (s₀.gpr .x0 + BitVec.ofNat 64 (8*j)) 64

theorem load_ok (s₀ : VG.AArch64.State)
    (hin : ∀ i < 25, InRegions (s₀.rd ++ s₀.wr)
      (s₀.gpr .x0 + BitVec.ofNat 64 (8*i)) 8) :
    WP isa (.block load) s₀ fun s' => Keep s₀ s' ∧ s'.mem = s₀.mem ∧ s'.v = s₀.v ∧
      Lanes s' (Spec.Sha3.stateAt s₀.mem (s₀.gpr .x0)) := by
  have hrun : ∀ s, LoadInv s₀ 0 s →
      WP isa (.block ((List.range 25).map fun i => .ldr .x (laneReg i) .x30 (8*i)))
        s (LoadInv s₀ 25) := by
    intro s hs
    rw [show (List.range 25).map (fun i => Instr.ldr .x (laneReg i) .x30 (8*i)) =
      (List.range 25).flatMap (fun i => [Instr.ldr .x (laneReg i) .x30 (8*i)]) by rfl]
    refine wp_range_flatMap (M := isa) (LoadInv s₀) (fun i s hi hs => ?_)
      25 (Nat.le_refl _) s hs
    refine WP.cons (exec_ldr_x ⟨by omega,by omega⟩ ?_) (wp_nil ?_)
    · rw [hs.keep.rd,hs.keep.wr,hs.base]
      exact hin i hi
    · refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.mem,hs.vec,?_,fun j hj => ?_⟩
      · simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,
          Ne.symm (laneReg_ne_x30 i hi),ite_false,hs.base]
      · simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,
          laneReg_inj j (by omega) i hi]
        split
        · rename_i he; subst j
          rw [hs.mem,hs.base]
        · exact hs.lanes j (by omega)
  unfold load
  refine WP.cons (exec_addImm_x (by decide)) ?_
  refine (hrun _ ?_).mono fun s hs => ⟨hs.keep,hs.mem,hs.vec,?_⟩
  · refine ⟨⟨rfl,rfl,rfl⟩,rfl,rfl,?_,fun _ h => absurd h (by omega)⟩
    simp only [RegUpd.gpr_write_self,State.read,Size.bits,BitVec.setWidth_eq,
      show BitVec.ofNat 64 0 = 0 by rfl]
    exact BitVec.add_zero _
  · intro i hi
    simpa only [Spec.Sha3.stateAt,Vector.getElem_ofFn,VG.Proof.Sha3.laneAddr] using hs.lanes i hi

end VG.Proof.Sha3.AArch64.Scalar.Boundary
