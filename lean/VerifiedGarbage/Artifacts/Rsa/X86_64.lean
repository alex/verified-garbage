import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified

/-! # RSA (RFC 8017) on x86-64 -/

namespace VG.Artifacts.Rsa.X86_64

def artifacts : List Artifact := [
  { Spec.Rsa.publicApi with
    target := X86_64.target
    doc := Spec.Rsa.publicApi.doc
      (notes := ["Baseline x86-64: Montgomery multiplication on 64-bit words, with R² mod n by \
        constant-time doublings and squarings, and the exponent scanned left to right, a square \
        per bit and a multiplication per set bit."])
    code := Impl.Bignum.X86_64.Public.code
    contract := Spec.Rsa.publicContract X86_64.abi
    verified := Proof.Bignum.X86_64.public_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Rsa.X86_64
