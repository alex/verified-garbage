import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Md5.X86_64.Shared

/-!
# MD5 (RFC 1321) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Md5.X86_64

def artifacts : List Artifact := [
  { Spec.Md5.compressApi with
    target := X86_64.target
    doc := Spec.Md5.compressApi.doc ["These three regions must not overlap each other, nor the \
      return address on the stack (distinct Rust objects never do)."]
    code := Impl.Md5.X86_64.compress
    contract := Spec.Md5.compressContract X86_64.abi
    verified := Proof.Md5.X86_64.Shared.compress },
  { Spec.Md5.initApi with
    target := X86_64.target
    doc := Spec.Md5.initApi.doc ["It must not overlap the return address on the stack (a Rust \
      object never does)."]
    code := Impl.Md5.X86_64.Stream.init
    contract := Spec.Md5.initContract X86_64.abi
    verified := Proof.Md5.X86_64.Shared.init },
  { Spec.Md5.updateApi with
    target := X86_64.target
    doc := Spec.Md5.updateApi.doc ["These three regions must not overlap each other, the return \
      address on the stack, or the 8 bytes of stack below it, where its call of `vg_md5_compress` \
      stores its return address (distinct Rust objects never do)."]
    code := Impl.Md5.X86_64.Stream.update
    contract := Spec.Md5.updateContract X86_64.abi 8
    verified := Proof.Md5.X86_64.Shared.update },
  { Spec.Md5.finalizeApi with
    target := X86_64.target
    doc := Spec.Md5.finalizeApi.doc ["These three regions must not overlap each other, the return \
      address on the stack, or the 8 bytes of stack below it, where its call of `vg_md5_compress` \
      stores its return address (distinct Rust objects never do)."]
    code := Impl.Md5.X86_64.Stream.finalize
    contract := Spec.Md5.finalizeContract X86_64.abi 8
    verified := Proof.Md5.X86_64.Shared.finalize }]

end VG.Artifacts.Md5.X86_64
