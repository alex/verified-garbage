import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Selftest.X86_64
import VerifiedGarbage.Proof.Selftest.X86_64.Shared

/-!
# The pipeline self-test on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`.
-/

namespace VG.Artifacts.Selftest.X86_64

def artifacts : List Artifact := [
  { target := X86_64.target
    module := "selftest"
    name := "vg_selftest_add"
    sig := Spec.Selftest.addSig
    doc := "Pipeline self-test: returns `a.wrapping_add(b)`.\n\n\
      Contract: `VG.Spec.Selftest.addContract`. No safety requirements."
    code := Impl.Selftest.X86_64.add
    contract := Spec.Selftest.addContract X86_64.abi
    verified := Proof.Selftest.X86_64.Shared.add }]

end VG.Artifacts.Selftest.X86_64
