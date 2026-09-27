import VerifiedGarbage.TCB.X86_64.Target

/-!
# Pipeline self-test

**Trusted** (as every file in `Spec/`). Not a cryptographic algorithm: a
deliberately trivial function that exercises the whole pipeline (spec →
implementation → proof → `Artifacts.lean` → Rust) so that the pipeline is
tested before any real primitive exists.
-/

namespace VG.Spec.Selftest

/-- Wrapping 64-bit addition. -/
def add (a b : BitVec 64) : BitVec 64 := a + b

open X86_64 in
/-- x86-64 contract for `vg_selftest_add(a: u64, b: u64) -> u64`: returns
`add a b` and does not modify memory. Both arguments are secret. -/
def addX86_64 : Contract X86_64.isa where
  pre _ := True
  post s s' := s'.gpr .rax = add (s.gpr .rdi) (s.gpr .rsi) ∧ s'.mem = s.mem
  pub _ _ := True

end VG.Spec.Selftest
