import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Scrypt.AArch64.Salsa
import VerifiedGarbage.Impl.Scrypt.AArch64.BlockMix
import VerifiedGarbage.Impl.Scrypt.AArch64.RoMix
import VerifiedGarbage.Proof.Scrypt.AArch64.Shared

/-!
# scrypt (RFC 7914): Salsa20/8, scryptBlockMix and scryptROMix on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Scrypt.AArch64

def artifacts : List Artifact := [
  { Spec.Scrypt.salsaApi with
    target := AArch64.target
    doc := Spec.Scrypt.salsaApi.doc ["`b` and `scratch` must not overlap each other, and neither \
      may wrap around the end of the address space (distinct Rust objects never do)."]
    code := Impl.Scrypt.AArch64.salsa
    contract := Spec.Scrypt.salsaContract AArch64.abi
    verified := Proof.Scrypt.AArch64.Shared.salsa
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Scrypt.blockMixApi with
    target := AArch64.target
    doc := Spec.Scrypt.blockMixApi.doc ["`b`, `y` and `scratch` must not overlap each other or the \
      16 bytes of stack below the stack pointer, where it saves its return address, and none may \
      wrap around the end of the address space (distinct Rust objects never do)."]
    code := Impl.Scrypt.AArch64.blockMix
    contract := Spec.Scrypt.blockMixContract AArch64.abi 16
    verified := Proof.Scrypt.AArch64.Shared.blockMix
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Scrypt.roMixApi with
    target := AArch64.target
    doc := Spec.Scrypt.roMixApi.doc ["`b`, `v` and `scratch` must not overlap each other or the 16 \
      bytes of stack below the stack pointer, where its calls of `vg_scrypt_blockmix` save their \
      return address, and none may wrap around the end of the address space (distinct Rust objects \
      never do)."]
    code := Impl.Scrypt.AArch64.roMix
    contract := Spec.Scrypt.roMixContract AArch64.abi 16
    verified := Proof.Scrypt.AArch64.Shared.roMix
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Scrypt.AArch64
