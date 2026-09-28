import VerifiedGarbage.Spec.Selftest
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Selftest.X86_64
import VerifiedGarbage.Proof.Framework.Semantics

/-! # Pipeline self-test: x86-64 proof -/

namespace VG.Proof.Selftest

open Spec.Selftest

open X86_64 in
/-- The x86-64 contract the proof is written against, for
`vg_selftest_add(a: u64, b: u64) -> u64`: returns
`add a b` and does not modify memory. Both arguments are secret. -/
def addX86_64 : Contract X86_64.isa where
  pre _ := True
  post s s' := s'.gpr .rax = add (s.gpr .rdi) (s.gpr .rsi) ∧ s'.mem = s.mem
  pub _ _ := True

end VG.Proof.Selftest

namespace VG.Proof.Selftest.X86_64

open VG.X86_64

theorem add_verified :
    Verified X86_64.target Impl.Selftest.X86_64.add Proof.Selftest.addX86_64 := by
  refine ⟨?_, ?_, ?_⟩
  · intro s _
    refine ⟨[], _, .block rfl, ?_, ?_, ?_⟩
    · simp [abiPreserved, calleeSaved, State.setReg, arithFlags, State.setFlags]
    · simp [State.setReg, arithFlags, State.setFlags, Spec.Selftest.add]
    · rfl
  · refine ConstantTime.of_silent fun s t s' _ h => ?_
    rw [Impl.Selftest.X86_64.add, Exec.block_iff] at h
    cases h
    rfl
  · exact ⟨⟨fun _ => 0, none, none, none, none, fun _ => 0, [], [], fun _ => 0⟩, trivial⟩

end VG.Proof.Selftest.X86_64
