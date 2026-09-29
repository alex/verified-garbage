import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha3.X86.Shared

/-!
# SHA-3 and SHAKE (FIPS 202) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Sha3.X86

def artifacts : List Artifact := [
  { Spec.Sha3.permuteApi with
    target := X86.target
    doc := Spec.Sha3.permuteApi.doc
    code := Impl.Sha3.X86.permute
    contract := Spec.Sha3.permuteContract X86.abi
    verified := Proof.Sha3.X86.Shared.permute
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Sha3.absorbApi with
    target := X86.target
    doc := Spec.Sha3.absorbApi.doc
    code := Impl.Sha3.X86.Stream.absorb
    contract := Spec.Sha3.absorbContract X86.abi 12
    stack := 12
    verified := Proof.Sha3.X86.Shared.absorb
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Sha3.padApi with
    target := X86.target
    doc := Spec.Sha3.padApi.doc
    code := Impl.Sha3.X86.Stream.pad
    contract := Spec.Sha3.padContract X86.abi 12
    stack := 12
    verified := Proof.Sha3.X86.Shared.pad
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Sha3.squeezeApi with
    target := X86.target
    doc := Spec.Sha3.squeezeApi.doc
    code := Impl.Sha3.X86.Stream.squeeze
    contract := Spec.Sha3.squeezeContract X86.abi 12
    stack := 12
    verified := Proof.Sha3.X86.Shared.squeeze
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Sha3.X86
