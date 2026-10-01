import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.X25519.X86_64
import VerifiedGarbage.Proof.X25519.X86_64.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Impl.X25519.X86_64.Adx
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
import VerifiedGarbage.Impl.X25519.X86_64.Ifma
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lit

/-!
# X25519 (RFC 7748) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.X25519.X86_64

def artifacts : List Artifact := [
  { Spec.X25519.x25519Api with
    target := X86_64.target
    doc := Spec.X25519.x25519Api.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are four 64-bit words, multiplied with `mul` \
      (squares computing each cross product once) and reduced with `2^256 = 38` (mod p); the \
      inversion is ref10's addition chain."])
    code := Impl.X25519.X86_64.x25519
    contract := Spec.X25519.x25519Contract X86_64.abi
    verified := Proof.X25519.X86_64.x25519_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.X25519.x25519Api with
    target := X86_64.target
    name := "vg_x25519_adx"
    doc := Spec.X25519.x25519Api.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are four 64-bit words, multiplied and squared with \
      BMI2's `mulx` and ADX's `adcx` and `adox` (two carry chains at once) and reduced with \
      `2^256 = 38` (mod p); the inversion is ref10's addition chain. The same code as \
      `vg_x25519` but for the field multiplications."])
    code := Impl.X25519.X86_64.x25519Adx
    contract := Spec.X25519.x25519Contract X86_64.abi
    verified := Proof.X25519.X86_64.x25519Adx_verified
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.X25519.x25519Api with
    target := X86_64.target
    name := "vg_x25519_ifma"
    doc := Spec.X25519.x25519Api.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. The ladder runs the four field multiplications of each of its \
      three stages at once, one to each 64-bit lane of `ymm` registers, with AVX512_IFMA's \
      `vpmadd52luq` and `vpmadd52huq`: field elements are five 51-bit limbs, reduced with \
      `2^255 = 19` (mod p). It sets MXCSR to `0x1FBF` for the ladder (Intel's mitigation of \
      MXCSR-configuration-dependent timing) and restores the caller's. The inversion is \
      ref10's addition chain, with `vg_x25519_adx`'s field multiplications."])
    code := Impl.X25519.X86_64.x25519Ifma
    contract := Spec.X25519.x25519Contract X86_64.abi
    verified := Proof.X25519.X86_64.x25519Ifma_verified
    features := ["avx", "avx2", "bmi2", "adx", "avx512ifma", "avx512vl"]
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.X25519.X86_64
