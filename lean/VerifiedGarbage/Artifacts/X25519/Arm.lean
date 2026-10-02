import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.X25519.Arm
import VerifiedGarbage.Proof.X25519.Arm.Verified

/-! # X25519 (RFC 7748) on ARMv7 -/

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
