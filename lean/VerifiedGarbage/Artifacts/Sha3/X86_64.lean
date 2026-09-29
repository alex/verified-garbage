import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha3.X86_64.Permute
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze

/-!
# SHA-3 and SHAKE (FIPS 202) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Sha3.X86_64

def artifacts : List Artifact := [
  { Spec.Sha3.permuteApi with
    target := X86_64.target
    doc := Spec.Sha3.permuteApi.doc
    code := Impl.Sha3.X86_64.permute
    contract := Spec.Sha3.permuteContract X86_64.abi
    verified := Proof.Sha3.X86_64.permute_verified },
  { Spec.Sha3.absorbApi with
    target := X86_64.target
    doc := Spec.Sha3.absorbApi.doc
    code := Impl.Sha3.X86_64.Stream.absorb
    contract := Spec.Sha3.absorbContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha3.X86_64.Stream.Absorb.absorb_verified },
  { Spec.Sha3.padApi with
    target := X86_64.target
    doc := Spec.Sha3.padApi.doc
    code := Impl.Sha3.X86_64.Stream.pad
    contract := Spec.Sha3.padContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha3.X86_64.Stream.Pad.pad_verified },
  { Spec.Sha3.squeezeApi with
    target := X86_64.target
    doc := Spec.Sha3.squeezeApi.doc
    code := Impl.Sha3.X86_64.Stream.squeeze
    contract := Spec.Sha3.squeezeContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha3.X86_64.Stream.Squeeze.squeeze_verified }]

end VG.Artifacts.Sha3.X86_64
