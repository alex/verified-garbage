import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Selftest.X86_64
import VerifiedGarbage.Proof.Selftest.X86_64

/-!
# The pipeline self-test on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
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
    verified := Proof.Selftest.X86_64.add_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Selftest.X86_64
