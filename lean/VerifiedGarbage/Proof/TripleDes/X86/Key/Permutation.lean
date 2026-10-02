import VerifiedGarbage.Proof.TripleDes.X86.Permutation

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.Impl.TripleDes.X86

theorem pc1_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc1 64 32 28 .eax .ebx .esi .edi .ecx) s = some s' ∧
      s'.gpr .eax = ((Spec.TripleDes.permute Spec.TripleDes.pc1 (packedInput 64 32 (s.gpr .esi) (s.gpr .edi))).setWidth 28).setWidth 32 ∧
      s'.gpr .ebx = (((Spec.TripleDes.permute Spec.TripleDes.pc1 (packedInput 64 32 (s.gpr .esi) (s.gpr .edi))) >>> 28).setWidth 28).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation1.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc1 (by decide) 32 28
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .esi .edi .eax .ebx (instrs keyPermutation1.lit) keyPermutation1_check (by decide +kernel) s
  have hcode : permuteCode Spec.TripleDes.pc1 64 32 28 .eax .ebx .esi .edi .ecx = instrs keyPermutation1.lit :=
    congrArg instrs keyPermutation1.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩


theorem pc2_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.pc2 56 28 32 .eax .ebx .edi .esi .ecx) s = some s' ∧
      s'.gpr .eax = ((Spec.TripleDes.permute Spec.TripleDes.pc2 (packedInput 56 28 (s.gpr .edi) (s.gpr .esi))).setWidth 32).setWidth 32 ∧
      s'.gpr .ebx = (((Spec.TripleDes.permute Spec.TripleDes.pc2 (packedInput 56 28 (s.gpr .edi) (s.gpr .esi))) >>> 32).setWidth 16).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs keyPermutation2.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.pc2 (by decide) 28 32
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .edi .esi .eax .ebx (instrs keyPermutation2.lit) keyPermutation2_check (by decide +kernel) s
  have hcode : permuteCode Spec.TripleDes.pc2 56 28 32 .eax .ebx .edi .esi .ecx = instrs keyPermutation2.lit :=
    congrArg instrs keyPermutation2.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩

end VG.Proof.TripleDes.X86.Key
