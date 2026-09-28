import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sha512.Arm.Shared

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Sha512.Arm

def artifacts : List Artifact := [
  { Spec.Sha512.compressApi with
    target := Arm.target
    doc := Spec.Sha512.compressApi.doc ["These three regions must not overlap each other, and none \
      of them may wrap around the end of the address space (no Rust object does)."]
    code := Impl.Sha512.Arm.compress
    contract := Spec.Sha512.compressContract Arm.abi
    verified := Proof.Sha512.Arm.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.init384Api with
    target := Arm.target
    doc := Spec.Sha512.init384Api.doc ["It must not wrap around the end of the address space (no \
      Rust object does)."]
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_384
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_384
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_384 },
  { Spec.Sha512.init512Api with
    target := Arm.target
    doc := Spec.Sha512.init512Api.doc ["It must not wrap around the end of the address space (no \
      Rust object does)."]
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_512
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512 },
  { Spec.Sha512.init512_224Api with
    target := Arm.target
    doc := Spec.Sha512.init512_224Api.doc ["It must not wrap around the end of the address space \
      (no Rust object does)."]
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_224
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_512_224
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_224 },
  { Spec.Sha512.init512_256Api with
    target := Arm.target
    doc := Spec.Sha512.init512_256Api.doc ["It must not wrap around the end of the address space \
      (no Rust object does)."]
    code := Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512_256
    contract := Spec.Sha512.initContract Arm.abi Spec.Sha512.H0_512_256
    verified := Proof.Sha512.Arm.Shared.init Spec.Sha512.H0_512_256 },
  { Spec.Sha512.updateApi with
    target := Arm.target
    doc := Spec.Sha512.updateApi.doc ["These three regions must not overlap each other, nor the \
      arguments passed on the stack, and none of them may wrap around the end of the address space \
      (distinct Rust objects never do)."]
    code := Impl.Sha512.Arm.Stream.update
    contract := Spec.Sha512.updateContract Arm.abi
    verified := Proof.Sha512.Arm.Shared.update
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha512.finalizeApi with
    target := Arm.target
    doc := Spec.Sha512.finalizeApi.doc ["These three regions must not overlap each other, nor the \
      arguments passed on the stack, and none of them may wrap around the end of the address space \
      (distinct Rust objects never do)."]
    code := Impl.Sha512.Arm.Stream.finalize
    contract := Spec.Sha512.finalizeContract Arm.abi
    verified := Proof.Sha512.Arm.Shared.finalize
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Sha512.Arm
