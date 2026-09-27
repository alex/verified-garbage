import VerifiedGarbage.Spec.Selftest
import VerifiedGarbage.Impl.Selftest.X86_64
import VerifiedGarbage.Proof.Framework.Semantics

/-! # Pipeline self-test: x86-64 proof -/

namespace VG.Proof.Selftest.X86_64

open VG.X86_64

theorem add_verified :
    Verified X86_64.target Impl.Selftest.X86_64.add Spec.Selftest.addX86_64 := by
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
  · exact ⟨⟨fun _ => 0, none, none, none, none, fun _ => 0, [], []⟩, trivial⟩

end VG.Proof.Selftest.X86_64
