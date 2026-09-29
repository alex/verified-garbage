import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.MlKem.X86.AddSub

/-!
# ML-KEM (FIPS 203) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

The functions that call no other one save their caller's registers in a
frame of 16 bytes below the return address (`stack := 16`).
-/

namespace VG.Artifacts.MlKem.X86

def artifacts : List Artifact := [
  { Spec.MlKem.addApi with
    target := X86.target
    doc := Spec.MlKem.addApi.doc
    code := Impl.MlKem.X86.add
    contract := Spec.MlKem.addContract X86.abi 16
    stack := 16
    verified := Proof.MlKem.X86.add_verified },
  { Spec.MlKem.subApi with
    target := X86.target
    doc := Spec.MlKem.subApi.doc
    code := Impl.MlKem.X86.sub
    contract := Spec.MlKem.subContract X86.abi 16
    stack := 16
    verified := Proof.MlKem.X86.sub_verified }]

end VG.Artifacts.MlKem.X86
