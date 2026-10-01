import VerifiedGarbage.Proof.TripleDes.AArch64.Permutation
import VerifiedGarbage.Proof.TripleDes.Core
namespace VG.Proof.TripleDes.AArch64
open VG VG.AArch64 VG.Impl.TripleDes.AArch64

theorem initial_ok (s : State) :
    ∃ s', runBlock isa (instrs initialPermutation.lit) s = some s' ∧
      s'.gpr .x10 = (Spec.TripleDes.permute Spec.TripleDes.ip
        ((s.gpr .x3).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) :=
  fixedPermutation_ok Spec.TripleDes.ip (by decide) (by decide)
    VG.Proof.TripleDes.ip_bounds .x3 .x10 (instrs initialPermutation.lit) initialPermutation_check s
end VG.Proof.TripleDes.AArch64
namespace VG.Proof.TripleDes.AArch64
open VG VG.AArch64 VG.Impl.TripleDes.AArch64

theorem initial_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.ip 64 .x10 .x3 .x11 .x12) s = some s' ∧
      s'.gpr .x10 = Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .x3) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, sp, mem, regs⟩ := initial_ok s
  have hcode : permuteCode Spec.TripleDes.ip 64 .x10 .x3 .x11 .x12 =
      instrs initialPermutation.lit := congrArg instrs initialPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, sp, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) (BitVec.setWidth_eq _)))
end VG.Proof.TripleDes.AArch64

namespace VG.Proof.TripleDes.AArch64
open VG VG.AArch64 VG.Impl.TripleDes.AArch64
theorem final_ok (s : State) :
    ∃ s', runBlock isa (instrs finalPermutation.lit) s = some s' ∧
      s'.gpr .x10 = (Spec.TripleDes.permute Spec.TripleDes.fp
        ((s.gpr .x3).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) :=
  fixedPermutation_ok Spec.TripleDes.fp (by decide) (by decide)
    VG.Proof.TripleDes.fp_bounds .x3 .x10 (instrs finalPermutation.lit) finalPermutation_check s

theorem final_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.fp 64 .x10 .x3 .x11 .x12) s = some s' ∧
      s'.gpr .x10 = Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .x3) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => dstOf op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, sp, mem, regs⟩ := final_ok s
  have hcode : permuteCode Spec.TripleDes.fp 64 .x10 .x3 .x11 .x12 =
      instrs finalPermutation.lit := congrArg instrs finalPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, sp, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.fp) (BitVec.setWidth_eq _)))

end VG.Proof.TripleDes.AArch64
