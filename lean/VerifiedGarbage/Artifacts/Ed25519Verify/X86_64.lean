import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.Window

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
      (Impl.Ed25519.X86_64.double4 Impl.X25519.X86_64.baseline)
    contract := Spec.Ed25519.verifyEquationContract X86_64.abi
    verified := Proof.Ed25519.X86_64.verify_verified (by lit_decide)
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
      (Impl.Ed25519.X86_64.double4 Impl.X25519.X86_64.adx)
    contract := Spec.Ed25519.verifyEquationContract X86_64.abi
    verified := Proof.Ed25519.X86_64.verify_verified (by lit_decide)
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ed25519.verifyEquationApi with
    target := X86_64.target
    name := "vg_ed25519_verify_equation_ifma"
    doc := Spec.Ed25519.verifyEquationApi.doc (notes := ["The code of \
      `vg_ed25519_verify_equation_adx` but for its doublings, four at a time, which hold the \
      point's coordinates `X, Y, Z, T` in the four lanes of `ymm` registers, as five 51-bit \
      limbs each, and double it with two four-lane multiplications (AVX512_IFMA's \
      `vpmadd52luq` and `vpmadd52huq` on `ymm` registers, with AVX512VL), as `vg_x25519_ifma`'s \
      ladder multiplies. Its inputs are public, so the multiplications do not run between \
      Intel's MXCSR prologue and epilogue."])
    code := Impl.Ed25519.X86_64.verifyEquation Impl.X25519.X86_64.adx Impl.Ed25519.X86_64.Ifma.double4
    contract := Spec.Ed25519.verifyEquationContract X86_64.abi
    verified := Proof.Ed25519.X86_64.verify_verified (by lit_decide)
    features := ["avx", "avx2", "bmi2", "adx", "avx512ifma", "avx512vl"]
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519Verify.X86_64
