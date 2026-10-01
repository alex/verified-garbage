import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure RestoreInv (orig s₀ : VG.AArch64.State) (k : Nat) (s : VG.AArch64.State) : Prop where
  keep : Keep s₀ s
  mem : s.mem = s₀.mem
  vec : s.v = s₀.v
  base : s.gpr .x17 = orig.gpr .x1
  vals : ∀ i < k, s.gpr (savedReg i) = orig.gpr (savedReg i)

theorem restore_ok (orig s₀ : VG.AArch64.State) (hsave : Saved orig s₀.mem)
    (hptr : vdword (s₀.v .v31) 0 = orig.gpr .x1)
    (hin : ∀ i < 11, InRegions (s₀.rd ++ s₀.wr)
      (orig.gpr .x1 + BitVec.ofNat 64 (8*i)) 8) :
    WP isa (.block restore) s₀ fun s' => Keep s₀ s' ∧ s'.mem = s₀.mem ∧ s'.v = s₀.v ∧
      ∀ r ∈ VG.AArch64.preserved, s'.gpr r = orig.gpr r := by
  have hrun : ∀ s, RestoreInv orig s₀ 0 s →
      WP isa (.block ((List.range 11).map fun i => .ldr .x (savedReg i) .x17 (8*i)))
        s (RestoreInv orig s₀ 11) := by
    intro s hs
    rw [show (List.range 11).map (fun i => Instr.ldr .x (savedReg i) .x17 (8*i)) =
      (List.range 11).flatMap (fun i => [Instr.ldr .x (savedReg i) .x17 (8*i)]) by rfl]
    refine wp_range_flatMap (M := isa) (RestoreInv orig s₀) (fun i s hi hr => ?_)
      11 (Nat.le_refl _) s hs
    refine WP.cons (exec_ldr_x ⟨by omega,by omega⟩ ?_) (wp_nil ?_)
    · rw [hr.keep.rd,hr.keep.wr,hr.base]
      exact hin i hi
    · refine ⟨⟨hr.keep.rd,hr.keep.wr,hr.keep.sp⟩,hr.mem,hr.vec,?_,fun j hj => ?_⟩
      · simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,
          Ne.symm (savedReg_ne_x17 i hi),ite_false,hr.base]
      · simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,
          savedReg_inj j (by omega) i hi]
        split
        · rename_i he; subst j
          rw [hr.mem,hr.base]
          exact hsave i hi
        · exact hr.vals j (by omega)
  unfold restore
  refine WP.cons rfl ?_
  refine (hrun _ ?_).mono fun s hs => ⟨hs.keep,hs.mem,hs.vec,fun r hr => ?_⟩
  · refine ⟨⟨rfl,rfl,rfl⟩,rfl,rfl,?_,fun _ h => absurd h (by omega)⟩
    simpa only [RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq,vdword] using hptr
  · have hv : ∀ r ∈ VG.AArch64.preserved, ∃ i : Fin 11, r = savedReg i.val := by decide
    obtain ⟨i,rfl⟩ := hv r hr
    exact hs.vals i.val i.isLt

end VG.Proof.Sha3.AArch64.Scalar.Boundary
