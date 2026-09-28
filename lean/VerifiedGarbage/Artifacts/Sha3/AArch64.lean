import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha3.AArch64.Shared

/-!
# SHA-3 and SHAKE (FIPS 202) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Sha3.AArch64

def artifacts : List Artifact := [
  { Spec.Sha3.permuteApi with
    target := AArch64.target
    doc := Spec.Sha3.permuteApi.doc ["These two regions must not overlap each other."]
    code := Impl.Sha3.AArch64.permute
    contract := Spec.Sha3.permuteContract AArch64.abi
    verified := Proof.Sha3.AArch64.Shared.permute
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.absorbApi with
    target := AArch64.target
    doc := Spec.Sha3.absorbApi.doc ["These three regions must not overlap each other, or the 16 \
      bytes of stack below the stack pointer, where it saves its return address before calling \
      `vg_keccak_f1600` (distinct Rust objects never do)."]
    code := Impl.Sha3.AArch64.Stream.absorb
    contract := Spec.Sha3.absorbContract AArch64.abi 16
    verified := Proof.Sha3.AArch64.Shared.absorb
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.padApi with
    target := AArch64.target
    doc := Spec.Sha3.padApi.doc ["These two regions must not overlap each other, or the 16 bytes \
      of stack below the stack pointer, where it saves its return address before calling \
      `vg_keccak_f1600` (distinct Rust objects never do)."]
    code := Impl.Sha3.AArch64.Stream.pad
    contract := Spec.Sha3.padContract AArch64.abi 16
    verified := Proof.Sha3.AArch64.Shared.pad
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha3.squeezeApi with
    target := AArch64.target
    doc := Spec.Sha3.squeezeApi.doc ["These three regions must not overlap each other, or the 16 \
      bytes of stack below the stack pointer, where it saves its return address before calling \
      `vg_keccak_f1600` (distinct Rust objects never do)."]
    code := Impl.Sha3.AArch64.Stream.squeeze
    contract := Spec.Sha3.squeezeContract AArch64.abi 16
    verified := Proof.Sha3.AArch64.Shared.squeeze
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha3.AArch64
