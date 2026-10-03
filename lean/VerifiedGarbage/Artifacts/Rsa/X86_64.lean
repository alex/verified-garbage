import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Proof.Bignum.X86_64.PdVerified

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
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Rsa.publicPrecomputeApi with
    target := X86_64.target
    doc := Spec.Rsa.publicPrecomputeApi.doc
      (notes := ["Baseline x86-64: R² mod n as `vg_rsa_public` computes it."])
    code := Impl.Rsa.X86_64.Precompute.code
    contract := Spec.Rsa.publicPrecomputeContract X86_64.abi
    verified := Proof.Bignum.X86_64.precompute_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Rsa.publicPrecomputedApi with
    target := X86_64.target
    doc := Spec.Rsa.publicPrecomputedApi.doc
      (notes := ["Baseline x86-64: `vg_rsa_public`'s Montgomery multiplication, with the exponent \
        scanned left to right from its first set bit, which starts the result as the input; a \
        square per later bit and a multiplication per later set bit. `pre` is checked (`n` odd, \
        its top word not zero, `R² mod n` below it) before any arithmetic, so that values of no \
        modulus are safe."])
    code := Impl.Rsa.X86_64.Precomputed.code
    contract := Spec.Rsa.publicPrecomputedContract X86_64.abi
    verified := Proof.Bignum.X86_64.precomputed_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Rsa.X86_64
