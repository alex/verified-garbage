import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha3.X86_64.Shared

/-!
# SHA-3 and SHAKE (FIPS 202) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Sha3.X86_64

def artifacts : List Artifact := [
  { Spec.Sha3.permuteApi with
    target := X86_64.target
    doc := Spec.Sha3.permuteApi.doc ["These two regions must not overlap each other, nor the \
      return address on the stack (distinct Rust objects never do)."]
    code := Impl.Sha3.X86_64.permute
    contract := Spec.Sha3.permuteContract X86_64.abi
    verified := Proof.Sha3.X86_64.Shared.permute },
  { Spec.Sha3.absorbApi with
    target := X86_64.target
    doc := Spec.Sha3.absorbApi.doc ["These three regions must not overlap each other, the return \
      address on the stack, or the 8 bytes of stack below it, where its call of `vg_keccak_f1600` \
      stores its return address (distinct Rust objects never do)."]
    code := Impl.Sha3.X86_64.Stream.absorb
    contract := Spec.Sha3.absorbContract X86_64.abi 8
    verified := Proof.Sha3.X86_64.Shared.absorb },
  { Spec.Sha3.padApi with
    target := X86_64.target
    doc := Spec.Sha3.padApi.doc ["These two regions must not overlap each other, the return \
      address on the stack, or the 8 bytes of stack below it, where its call of `vg_keccak_f1600` \
      stores its return address (distinct Rust objects never do)."]
    code := Impl.Sha3.X86_64.Stream.pad
    contract := Spec.Sha3.padContract X86_64.abi 8
    verified := Proof.Sha3.X86_64.Shared.pad },
  { Spec.Sha3.squeezeApi with
    target := X86_64.target
    doc := Spec.Sha3.squeezeApi.doc ["These three regions must not overlap each other, the return \
      address on the stack, or the 8 bytes of stack below it, where its call of `vg_keccak_f1600` \
      stores its return address (distinct Rust objects never do)."]
    code := Impl.Sha3.X86_64.Stream.squeeze
    contract := Spec.Sha3.squeezeContract X86_64.abi 8
    verified := Proof.Sha3.X86_64.Shared.squeeze }]

end VG.Artifacts.Sha3.X86_64
