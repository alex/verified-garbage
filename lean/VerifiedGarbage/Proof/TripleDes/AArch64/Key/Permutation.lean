import VerifiedGarbage.Proof.TripleDes.AArch64.Permutation

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

 theorem pc1_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc1 64 .x5 .x4 .x6 .x7) s = some s' ∧
      s'.gpr .x5 = (Spec.TripleDes.permute Spec.TripleDes.pc1 (s.gpr .x4)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation1.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc1 (by decide) (by decide) (by decide)
       .x4 .x5 (instrs keyPermutation1.lit) keyPermutation1_check s
  have hcode : permuteCode Spec.TripleDes.pc1 64 .x5 .x4 .x6 .x7 = instrs keyPermutation1.lit :=
    congrArg instrs keyPermutation1.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, sp, mem, regs⟩
  exact word.trans (congrArg (fun x => (Spec.TripleDes.permute Spec.TripleDes.pc1 x).setWidth 64)
    (BitVec.setWidth_eq _))

theorem pc2_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc2 56 .x5 .x4 .x6 .x7) s = some s' ∧
      s'.gpr .x5 = (Spec.TripleDes.permute Spec.TripleDes.pc2 ((s.gpr .x4).setWidth 56)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation2.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc2 (by decide) (by decide) (by decide)
       .x4 .x5 (instrs keyPermutation2.lit) keyPermutation2_check s
  have hcode : permuteCode Spec.TripleDes.pc2 56 .x5 .x4 .x6 .x7 = instrs keyPermutation2.lit :=
    congrArg instrs keyPermutation2.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, word, rd, wr, sp, mem, regs⟩

end VG.Proof.TripleDes.AArch64.Key
