import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha512.X86_64.Shared

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Sha512.X86_64

def artifacts : List Artifact := [
  { Spec.Sha512.compressApi with
    target := X86_64.target
    doc := Spec.Sha512.compressApi.doc ["These three regions must not overlap each other, nor the \
      return address on the stack (distinct Rust objects never do)."]
    code := Impl.Sha512.X86_64.compress
    contract := Spec.Sha512.compressContract X86_64.abi
    verified := Proof.Sha512.X86_64.Shared.compress },
  { Spec.Sha512.init384Api with
    target := X86_64.target
    doc := Spec.Sha512.init384Api.doc ["It must not overlap the return address on the stack (a \
      Rust object never does)."]
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_384
    contract := Spec.Sha512.initContract X86_64.abi Spec.Sha512.H0_384
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_384 },
  { Spec.Sha512.init512Api with
    target := X86_64.target
    doc := Spec.Sha512.init512Api.doc ["It must not overlap the return address on the stack (a \
      Rust object never does)."]
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512
    contract := Spec.Sha512.initContract X86_64.abi Spec.Sha512.H0_512
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_512 },
  { Spec.Sha512.init512_224Api with
    target := X86_64.target
    doc := Spec.Sha512.init512_224Api.doc ["It must not overlap the return address on the stack (a \
      Rust object never does)."]
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_224
    contract := Spec.Sha512.initContract X86_64.abi Spec.Sha512.H0_512_224
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_512_224 },
  { Spec.Sha512.init512_256Api with
    target := X86_64.target
    doc := Spec.Sha512.init512_256Api.doc ["It must not overlap the return address on the stack (a \
      Rust object never does)."]
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_256
    contract := Spec.Sha512.initContract X86_64.abi Spec.Sha512.H0_512_256
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_512_256 },
  { Spec.Sha512.updateApi with
    target := X86_64.target
    doc := Spec.Sha512.updateApi.doc ["These three regions must not overlap each other, the return \
      address on the stack, or the 8 bytes of stack below it, where its call of \
      `vg_sha512_compress` stores its return address (distinct Rust objects never do)."]
    code := Impl.Sha512.X86_64.Stream.update
    contract := Spec.Sha512.updateContract X86_64.abi 8
    verified := Proof.Sha512.X86_64.Shared.update },
  { Spec.Sha512.finalizeApi with
    target := X86_64.target
    doc := Spec.Sha512.finalizeApi.doc ["These three regions must not overlap each other, the \
      return address on the stack, or the 8 bytes of stack below it, where its call of \
      `vg_sha512_compress` stores its return address (distinct Rust objects never do)."]
    code := Impl.Sha512.X86_64.Stream.finalize
    contract := Spec.Sha512.finalizeContract X86_64.abi 8
    verified := Proof.Sha512.X86_64.Shared.finalize }]

end VG.Artifacts.Sha512.X86_64
