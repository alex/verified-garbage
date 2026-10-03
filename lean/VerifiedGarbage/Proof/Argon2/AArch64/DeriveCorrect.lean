import VerifiedGarbage.Proof.Argon2.AArch64.DeriveReturn
import VerifiedGarbage.Proof.Argon2.AArch64.DerivePreserved

/-! Functional correctness, termination, memory safety, and the ARM64 ABI. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

theorem code_correct (v : HPrime.Backend) (name : String) (s : State)
    (pre : (Spec.Argon2.deriveContract AArch64.abi 400).pre s) :
    ∃ tr t, Exec isa (Impl.Argon2.AArch64.Derive.code name v.hash) s tr t ∧
      abiPreserved s t ∧ (Spec.Argon2.deriveContract AArch64.abi 400).post s t := by
  obtain ⟨tr, t, run, post, regs, sp, frame⟩ := code_wp v name s pre
  exact ⟨tr, t, run, ⟨regs, sp, Exec.preservedV run (code_preservedV v name)⟩, post⟩
end VG.Proof.Argon2.AArch64.Derive
