import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit

/-! # ECDSA over P-256 (FIPS 186-5) on x86-64 -/

namespace VG.Artifacts.EcdsaP256.X86_64

def artifacts : List Artifact := [
  { Spec.Ecdsa.P256.signApi with
    target := X86_64.target
    doc := Spec.Ecdsa.P256.signApi.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements and scalars are four 64-bit words in Montgomery \
      form, multiplied by word-by-word Montgomery multiplication (CIOS) with a final \
      conditional subtraction. `[k]G` is a double-and-add ladder over all 256 bits of `k`, \
      with the complete addition formulas of Renes, Costello and Batina for every addition \
      and doubling and a masked selection for each bit; the inversions modulo `p` and `n` are \
      Fermat's, by square-and-always-multiply over the bits of `p - 2` and `n - 2`. The \
      signature (or zeros) is selected by a mask, so the time depends only on the pointers."])
    code := Impl.Ecdsa.X86_64.signP256
    contract := Spec.Ecdsa.P256.inst.signContract X86_64.abi
    verified := Proof.Ecdsa.X86_64.sign_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ecdsa.P256.verifyApi with
    target := X86_64.target
    doc := Spec.Ecdsa.P256.verifyApi.doc (notes := ["The function is `vg_ecdsa_p256_sign`'s setup, \
      field arithmetic, ladder and inversions, with `vg_ecdh_p256`'s checks of the public key: it \
      saves its caller's callee-saved registers in `scratch`; field elements and scalars are four \
      64-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication \
      (CIOS) with a final conditional subtraction. The key is checked without branches (its \
      first byte, both coordinates below `p`, and the curve's equation), and the second ladder \
      multiplies the key's point if it is valid, else `G`, so it always runs on a point of the \
      curve. `s⁻¹` modulo `n` and `Z⁻¹` are Fermat's, by square-and-always-multiply; `[u]G` and \
      `[v]Q` are double-and-add ladders over all 256 bits of `u` and `v`, with the complete \
      addition formulas of Renes, Costello and Batina, which also add the two. The result is \
      the conjunction of the checks (the key, `r` and `s` in `[1, n-1]`, the sum not the point \
      at infinity, and `x ≡ r` modulo `n`) as a mask, so the time depends only on the pointers, \
      although the contract would let every input affect it."])
    code := Impl.Ecdsa.Verify.X86_64.verifyP256
    contract := Spec.Ecdsa.P256.inst.verifyContract X86_64.abi
    verified := Proof.Ecdsa.Verify.X86_64.verify_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.EcdsaP256.X86_64
