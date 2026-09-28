import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Scrypt.X86_64.Salsa
import VerifiedGarbage.Impl.Scrypt.X86_64.BlockMix
import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix
import VerifiedGarbage.Proof.Scrypt.X86_64.Shared

/-!
# scrypt (RFC 7914): Salsa20/8, scryptBlockMix and scryptROMix on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Scrypt.X86_64

def artifacts : List Artifact := [
  { Spec.Scrypt.salsaApi with
    target := X86_64.target
    doc := Spec.Scrypt.salsaApi.doc ["`b` and `scratch` must not overlap each other, nor the \
      return address on the stack, and neither may wrap around the end of the address space \
      (distinct Rust objects never do)."]
    code := Impl.Scrypt.X86_64.salsa
    contract := Spec.Scrypt.salsaContract X86_64.abi
    verified := Proof.Scrypt.X86_64.Shared.salsa },
  { Spec.Scrypt.blockMixApi with
    target := X86_64.target
    doc := Spec.Scrypt.blockMixApi.doc ["`b`, `y` and `scratch` must not overlap each other, the \
      return address on the stack, or the 8 bytes of stack below it, where its calls of \
      `vg_salsa20_8` store their return address, and none may wrap around the end of the address \
      space (distinct Rust objects never do)."]
    code := Impl.Scrypt.X86_64.blockMix
    contract := Spec.Scrypt.blockMixContract X86_64.abi 8
    verified := Proof.Scrypt.X86_64.Shared.blockMix },
  { Spec.Scrypt.roMixApi with
    target := X86_64.target
    doc := Spec.Scrypt.roMixApi.doc ["`b`, `v` and `scratch` must not overlap each other, the \
      return address on the stack, or the 16 bytes of stack below it, where its calls store their \
      return addresses, and none may wrap around the end of the address space (distinct Rust \
      objects never do)."]
    code := Impl.Scrypt.X86_64.roMix
    contract := Spec.Scrypt.roMixContract X86_64.abi 16
    verified := Proof.Scrypt.X86_64.Shared.roMix }]

end VG.Artifacts.Scrypt.X86_64
