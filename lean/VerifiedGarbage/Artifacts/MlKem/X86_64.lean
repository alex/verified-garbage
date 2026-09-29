import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.AddSub

/-!
# ML-KEM (FIPS 203) on x86-64: the polynomial primitives and ML-KEM-768

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlKem.X86_64

def artifacts : List Artifact := [
  { Spec.MlKem.addApi with
    target := X86_64.target
    doc := Spec.MlKem.addApi.doc
    code := Impl.MlKem.X86_64.add
    contract := Spec.MlKem.addContract X86_64.abi
    verified := Proof.MlKem.X86_64.add_verified },
  { Spec.MlKem.subApi with
    target := X86_64.target
    doc := Spec.MlKem.subApi.doc
    code := Impl.MlKem.X86_64.sub
    contract := Spec.MlKem.subContract X86_64.abi
    verified := Proof.MlKem.X86_64.sub_verified }]

end VG.Artifacts.MlKem.X86_64
