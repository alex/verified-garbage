import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.X25519.AArch64
import VerifiedGarbage.Proof.X25519.AArch64.Verified

/-! # X25519 (RFC 7748) on AArch64 -/

namespace VG.Artifacts.X25519.AArch64

def artifacts : List Artifact := [
  { Spec.X25519.x25519Api with
    target := AArch64.target
    doc := Spec.X25519.x25519Api.doc (notes := ["The function saves the callee-saved registers \
      it uses (`x19`–`x24`) in `scratch`. Field elements are fifteen limbs of 17 bits \
      (`2^255 = 19` mod p), each in a 64-bit word, multiplied with `mul`/`madd` (which keep \
      the low 64 bits) and carried with explicit bounds; the inversion is square-and-multiply \
      over the bits of `p - 2`."])
    code := Impl.X25519.AArch64.x25519
    contract := Spec.X25519.x25519Contract AArch64.abi
    verified := Proof.X25519.AArch64.x25519_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.X25519.AArch64
