import VerifiedGarbage.Proof.TripleDes.Arm.Permutation
import VerifiedGarbage.Proof.TripleDes.Core

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Impl.TripleDes.Arm

theorem initial_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.ip 64 32 32 .r11 .r10 .r5 .r4 .r12 .r9) s = some s' ∧
      s'.gpr .r11 = (Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .r4 ++ s.gpr .r5)).setWidth 32 ∧
      s'.gpr .r10 = ((Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .r4 ++ s.gpr .r5)) >>> 32).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.ip (by decide) 32 32
      (by decide) (by decide) (by decide) (by decide) VG.Proof.TripleDes.ip_bounds
      .r5 .r4 .r11 .r10 (instrs initialPermutation.lit) initialPermutation_check s
  have hcode : permuteCode Spec.TripleDes.ip 64 32 32 .r11 .r10 .r5 .r4 .r12 .r9 = instrs initialPermutation.lit :=
    congrArg instrs initialPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, ?_, rd, wr, sp, mem, regs⟩
  · simpa only [packedInput, BitVec.setWidth_eq] using lo
  · simpa only [packedInput, BitVec.setWidth_eq] using hi


theorem final_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.fp 64 32 32 .r5 .r4 .r11 .r10 .r12 .r9) s = some s' ∧
      s'.gpr .r5 = (Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .r10 ++ s.gpr .r11)).setWidth 32 ∧
      s'.gpr .r4 = ((Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .r10 ++ s.gpr .r11)) >>> 32).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.fp (by decide) 32 32
      (by decide) (by decide) (by decide) (by decide) VG.Proof.TripleDes.fp_bounds
      .r11 .r10 .r5 .r4 (instrs finalPermutation.lit) finalPermutation_check s
  have hcode : permuteCode Spec.TripleDes.fp 64 32 32 .r5 .r4 .r11 .r10 .r12 .r9 = instrs finalPermutation.lit :=
    congrArg instrs finalPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, ?_, rd, wr, sp, mem, regs⟩
  · simpa only [packedInput, BitVec.setWidth_eq] using lo
  · simpa only [packedInput, BitVec.setWidth_eq] using hi

end VG.Proof.TripleDes.Arm
