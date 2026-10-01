import VerifiedGarbage.Proof.TripleDes.X86_64.Permutation
import VerifiedGarbage.Proof.TripleDes.Core
namespace VG.Proof.TripleDes.X86_64
open VG VG.X86_64 VG.Impl.TripleDes.X86_64

theorem initial_ok (s : State) :
    ∃ s', runBlock isa (instrs initialPermutation.lit) s = some s' ∧
      s'.gpr .rbx = (Spec.TripleDes.permute Spec.TripleDes.ip
        ((s.gpr .rax).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) :=
  fixedPermutation_ok Spec.TripleDes.ip (by decide) (by decide)
    VG.Proof.TripleDes.ip_bounds (instrs initialPermutation.lit) initialPermutation_check s
end VG.Proof.TripleDes.X86_64
namespace VG.Proof.TripleDes.X86_64
open VG VG.X86_64 VG.Impl.TripleDes.X86_64

theorem initial_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.ip 64 .rbx .rax .rbp) s = some s' ∧
      s'.gpr .rbx = Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .rax) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ := initial_ok s
  have hcode : permuteCode Spec.TripleDes.ip 64 .rbx .rax .rbp =
      instrs initialPermutation.lit := congrArg instrs initialPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) (BitVec.setWidth_eq _)))
end VG.Proof.TripleDes.X86_64
