import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Selftest.X86_64
import VerifiedGarbage.Spec.Selftest.Contract

/-!
# Pipeline self-test on X86_64: the shared contract

Untrusted: everything here is checked by Lean. The proof is written against
an x86-64 contract (`Proof/Selftest/X86_64.lean`); this theorem moves it to
the shared contract of `Spec/Selftest/Contract.lean`, which the artifact is
emitted with.
-/

namespace VG.Proof.Selftest.X86_64.Shared

/-- A state satisfying the precondition. -/
def sat : X86_64.State where
  gpr _ := 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := []

theorem add :
    Verified X86_64.target Impl.Selftest.X86_64.add (Spec.Selftest.addContract X86_64.abi) :=
  Proof.Selftest.X86_64.add_verified.of_implies (by
    contract_implies [Spec.Selftest.addContract, Spec.Selftest.addSig, Proof.Selftest.addX86_64,
      X86_64.abi, X86_64.argRegs]
      [sat] using sat)

end VG.Proof.Selftest.X86_64.Shared
