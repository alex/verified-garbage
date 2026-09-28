import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha1.AArch64.Shared

/-!
# SHA-1 (FIPS 180-4) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Sha1.AArch64

def artifacts : List Artifact := [
  { Spec.Sha1.compressApi with
    target := AArch64.target
    doc := Spec.Sha1.compressApi.doc ["These three regions must not overlap each other."]
    code := Impl.Sha1.AArch64.compress
    contract := Spec.Sha1.compressContract AArch64.abi
    verified := Proof.Sha1.AArch64.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha1.initApi with
    target := AArch64.target
    doc := Spec.Sha1.initApi.doc []
    code := Impl.Sha1.AArch64.Stream.init
    contract := Spec.Sha1.initContract AArch64.abi
    verified := Proof.Sha1.AArch64.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha1.updateApi with
    target := AArch64.target
    doc := Spec.Sha1.updateApi.doc ["These three regions must not overlap each other, or the 16 \
      bytes of stack below the stack pointer, where it saves its return address around its calls \
      of `vg_sha1_compress` (distinct Rust objects never do)."]
    code := Impl.Sha1.AArch64.Stream.update
    contract := Spec.Sha1.updateContract AArch64.abi 16
    verified := Proof.Sha1.AArch64.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha1.finalizeApi with
    target := AArch64.target
    doc := Spec.Sha1.finalizeApi.doc ["These three regions must not overlap each other, or the 16 \
      bytes of stack below the stack pointer, where it saves its return address around its calls \
      of `vg_sha1_compress` (distinct Rust objects never do)."]
    code := Impl.Sha1.AArch64.Stream.finalize
    contract := Spec.Sha1.finalizeContract AArch64.abi 16
    verified := Proof.Sha1.AArch64.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha1.AArch64
