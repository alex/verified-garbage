import VerifiedGarbage.Proof.TripleDes.Arm.Permutation

namespace VG.Proof.TripleDes.Arm.Key
open VG VG.Arm VG.Impl.TripleDes.Arm

theorem pc1_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc1 64 32 28 .r11 .r10 .r5 .r4 .r12 .lr) s = some s' ∧
      s'.gpr .r11 = ((Spec.TripleDes.permute Spec.TripleDes.pc1 (packedInput 64 32 (s.gpr .r5) (s.gpr .r4))).setWidth 28).setWidth 32 ∧
      s'.gpr .r10 = (((Spec.TripleDes.permute Spec.TripleDes.pc1 (packedInput 64 32 (s.gpr .r5) (s.gpr .r4))) >>> 28).setWidth 28).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation1.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc1 (by decide) 32 28
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .r5 .r4 .r11 .r10 (instrs keyPermutation1.lit) keyPermutation1_check s
  have hcode : permuteCode Spec.TripleDes.pc1 64 32 28 .r11 .r10 .r5 .r4 .r12 .lr = instrs keyPermutation1.lit :=
    congrArg instrs keyPermutation1.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩


theorem pc2_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc2 56 28 32 .r4 .r5 .r11 .r10 .r12 .lr) s = some s' ∧
      s'.gpr .r4 = ((Spec.TripleDes.permute Spec.TripleDes.pc2 (packedInput 56 28 (s.gpr .r11) (s.gpr .r10))).setWidth 32).setWidth 32 ∧
      s'.gpr .r5 = (((Spec.TripleDes.permute Spec.TripleDes.pc2 (packedInput 56 28 (s.gpr .r11) (s.gpr .r10))) >>> 32).setWidth 16).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation2.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc2 (by decide) 28 32
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .r11 .r10 .r4 .r5 (instrs keyPermutation2.lit) keyPermutation2_check s
  have hcode : permuteCode Spec.TripleDes.pc2 56 28 32 .r4 .r5 .r11 .r10 .r12 .lr = instrs keyPermutation2.lit :=
    congrArg instrs keyPermutation2.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩

end VG.Proof.TripleDes.Arm.Key
