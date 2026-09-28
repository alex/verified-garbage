import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha512.AArch64.Shared

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Sha512.AArch64

def artifacts : List Artifact := [
  { Spec.Sha512.compressApi with
    target := AArch64.target
    doc := Spec.Sha512.compressApi.doc ["These three regions must not overlap each other."]
    code := Impl.Sha512.AArch64.compress
    contract := Spec.Sha512.compressContract AArch64.abi
    verified := Proof.Sha512.AArch64.Shared.compress },
  { Spec.Sha512.init384Api with
    target := AArch64.target
    doc := Spec.Sha512.init384Api.doc []
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_384
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_384
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_384 },
  { Spec.Sha512.init512Api with
    target := AArch64.target
    doc := Spec.Sha512.init512Api.doc []
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_512
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512 },
  { Spec.Sha512.init512_224Api with
    target := AArch64.target
    doc := Spec.Sha512.init512_224Api.doc []
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512_224
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_512_224
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512_224 },
  { Spec.Sha512.init512_256Api with
    target := AArch64.target
    doc := Spec.Sha512.init512_256Api.doc []
    code := Impl.Sha512.AArch64.Stream.init Spec.Sha512.H0_512_256
    contract := Spec.Sha512.initContract AArch64.abi Spec.Sha512.H0_512_256
    verified := Proof.Sha512.AArch64.Shared.init Spec.Sha512.H0_512_256 },
  { Spec.Sha512.updateApi with
    target := AArch64.target
    doc := Spec.Sha512.updateApi.doc ["These three regions must not overlap each other."]
    code := Impl.Sha512.AArch64.Stream.update
    contract := Spec.Sha512.updateContract AArch64.abi
    verified := Proof.Sha512.AArch64.Shared.update },
  { Spec.Sha512.finalizeApi with
    target := AArch64.target
    doc := Spec.Sha512.finalizeApi.doc ["These three regions must not overlap each other."]
    code := Impl.Sha512.AArch64.Stream.finalize
    contract := Spec.Sha512.finalizeContract AArch64.abi
    verified := Proof.Sha512.AArch64.Shared.finalize }]

end VG.Artifacts.Sha512.AArch64
