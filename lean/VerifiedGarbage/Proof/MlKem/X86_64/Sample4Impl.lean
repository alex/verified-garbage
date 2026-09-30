import VerifiedGarbage.Proof.MlKem.X86_64.S4Scalar
import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim

/-!
# Implementations of `vg_mlkem_sample_ntt4` on x86-64

Untrusted: everything here is checked by Lean.

A `Sample4Impl` is what a function that calls `vg_mlkem_sample_ntt4` needs
of it, so that its proof holds for every implementation: each is a variant
of the interface `MlKemSample4` on x86-64 (`Variants/MlKemSample4/X86_64/`),
and each caller (the top-level functions of ML-KEM-768 and ML-KEM-1024, in
`Generic/MlKemSample4/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`). Both implementations use 24 bytes of stack below their
return address (`vg_mlkem_sample_ntt`'s calls, three deep).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- An implementation of `vg_mlkem_sample_ntt4` on x86-64. -/
structure Sample4Impl where
  /-- Its symbol and code. -/
  callee : Impl.MlKem.X86_64.Callee4
  /-- It is correct. -/
  ok : ∀ s, sample4K.pre s → ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ sample4K.post s s'
  /-- It is constant time. -/
  ct : ConstantTime isa sample4K.pre sample4K.pub callee.code
  /-- It never writes the stack pointer. -/
  nosp : NoSp callee.code
  /-- Its calls are at most three deep. -/
  depth_le : callee.code.depth ≤ 3
  /-- It never loads MXCSR. -/
  mxcsr : callee.code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- What the names of its callers' instances end with (e.g. `_avx2`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace Sample4Impl

/-- The baseline implementation, `vg_mlkem_sample_ntt4`, which calls `vg_mlkem_sample_ntt`. -/
def scalar : Sample4Impl where
  callee := .scalar
  ok := S4.correct_scalar
  ct := S4.ct_scalar
  nosp := nosp_of (by decide +kernel)
  depth_le := by decide +kernel
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := ""
  features := []

/-- The AVX2 implementation, `vg_mlkem_sample_ntt4_avx2`. -/
def avx2 : Sample4Impl where
  callee := .avx2
  ok := S4.correct
  ct := S4.ct
  nosp := nosp_of (by decide +kernel)
  depth_le := by decide +kernel
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := "_avx2"
  features := ["avx", "avx2"]

end Sample4Impl

end VG.Proof.MlKem.X86_64
