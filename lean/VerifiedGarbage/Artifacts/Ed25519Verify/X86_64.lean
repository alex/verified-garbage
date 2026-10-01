import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyVerified

/-! Complete strict Ed25519 equation verification with a caller-supplied SHA-512 challenge. -/

namespace VG.Artifacts.Ed25519Verify.X86_64

def artifacts : List Artifact := [
  { Spec.Ed25519.verifyEquationApi with
    target := X86_64.target
    doc := Spec.Ed25519.verifyEquationApi.doc (notes := ["Uses baseline integer instructions. \
      Checks canonical point encodings and S < L, then evaluates the uncofactored equation \
      using all 512 challenge bits. No additional subgroup or small-order policy is imposed. \
      Computes [k]A - [S]B with one chain of doublings and 4-bit windows of the public \
      scalars, from a table of [1]A to [15]A and constant -[1]B to -[15]B, and compares it \
      with -R projectively."])
    code := Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.baseline
    contract := Spec.Ed25519.verifyEquationContract X86_64.abi
    verified := Proof.Ed25519.X86_64.verify_verified (fld := Impl.X25519.X86_64.baseline)
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ed25519.verifyEquationApi with
    target := X86_64.target
    name := "vg_ed25519_verify_equation_adx"
    doc := Spec.Ed25519.verifyEquationApi.doc (notes := ["The code of \
      `vg_ed25519_verify_equation` but for the field multiplications and squarings, which use \
      BMI2's `mulx` and ADX's `adcx` and `adox` (two carry chains at once), as `vg_x25519_adx` \
      does. Checks canonical point encodings and S < L, then evaluates the uncofactored \
      equation using all 512 challenge bits, with one chain of doublings and 4-bit windows of \
      the public scalars."])
    code := Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.adx
    contract := Spec.Ed25519.verifyEquationContract X86_64.abi
    verified := Proof.Ed25519.X86_64.verify_verified (fld := Impl.X25519.X86_64.adx)
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519Verify.X86_64
