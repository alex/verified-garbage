import VerifiedGarbage.Proof.TripleDes.X86_64.Permutation

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

 theorem pc1_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc1 64 .rbx .rax .rbp) s = some s' ∧
      s'.gpr .rbx = (Spec.TripleDes.permute Spec.TripleDes.pc1 (s.gpr .rax)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation1.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc1 (by decide) (by decide) (by decide)
      (instrs keyPermutation1.lit) keyPermutation1_check s
  have hcode : permuteCode Spec.TripleDes.pc1 64 .rbx .rax .rbp = instrs keyPermutation1.lit :=
    congrArg instrs keyPermutation1.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, mem, regs⟩
  exact word.trans (congrArg (fun x => (Spec.TripleDes.permute Spec.TripleDes.pc1 x).setWidth 64)
    (BitVec.setWidth_eq _))

theorem pc2_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc2 56 .rbx .rax .rbp) s = some s' ∧
      s'.gpr .rbx = (Spec.TripleDes.permute Spec.TripleDes.pc2 ((s.gpr .rax).setWidth 56)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation2.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc2 (by decide) (by decide) (by decide)
      (instrs keyPermutation2.lit) keyPermutation2_check s
  have hcode : permuteCode Spec.TripleDes.pc2 56 .rbx .rax .rbp = instrs keyPermutation2.lit :=
    congrArg instrs keyPermutation2.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, word, rd, wr, mem, regs⟩

end VG.Proof.TripleDes.X86_64.Key
