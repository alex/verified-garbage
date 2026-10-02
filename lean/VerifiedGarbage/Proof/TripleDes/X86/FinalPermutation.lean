import VerifiedGarbage.Proof.TripleDes.X86.Initial
import VerifiedGarbage.Proof.TripleDes.X86.WordStore
import VerifiedGarbage.Proof.TripleDes.Word

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

theorem fp_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.fp 64 32 32 .eax .ebx .edi .esi .ecx) s = some s' ∧
      s'.gpr .eax = (Spec.TripleDes.permute Spec.TripleDes.fp
        (packedInput 64 32 (s.gpr .edi) (s.gpr .esi))).setWidth 32 ∧
      s'.gpr .ebx = ((Spec.TripleDes.permute Spec.TripleDes.fp
        (packedInput 64 32 (s.gpr .edi) (s.gpr .esi))) >>> 32).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.fp (by decide) 32 32
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .edi .esi .eax .ebx (instrs finalPermutation.lit) finalPermutation_check (by decide +kernel) s
  have hcode : permuteCode Spec.TripleDes.fp 64 32 32 .eax .ebx .edi .esi .ecx = instrs finalPermutation.lit :=
    congrArg instrs finalPermutation.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩

end VG.Proof.TripleDes.X86
