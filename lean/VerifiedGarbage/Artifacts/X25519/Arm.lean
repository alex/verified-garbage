import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.X25519.Arm
import VerifiedGarbage.Proof.X25519.Arm.Verified

/-!
# X25519 (RFC 7748) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.X25519.Arm

def artifacts : List Artifact := [
  { Spec.X25519.x25519Api with
    target := Arm.target
    doc := Spec.X25519.x25519Api.doc (notes := ["The function saves `r4`–`r11` in `scratch`. Its only \
      multiplication is `mul` (the low 32 bits of a 32 × 32-bit product): field elements are sixteen \
      16-bit limbs, multiplied row by row and reduced with `2^256 = 38` (mod p); the inversion is \
      square-and-multiply over the public bits of `p - 2`."])
    code := Impl.X25519.Arm.x25519
    contract := Spec.X25519.x25519Contract Arm.abi
    verified := Proof.X25519.Arm.x25519_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.X25519.Arm
