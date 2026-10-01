import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YBits
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YUse

/-!
# ML-DSA (FIPS 204) on x86-64: rounding and hints

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there. The emitter adds the `# Safety` items that
depend on the target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which
`ofSig` checks against the contract.
-/

namespace VG.Artifacts.MlDsaRound.X86_64

open VG.Proof.MlDsa.X86_64.Round

def artifacts : List Artifact := [
  { Spec.MlDsa.power2RoundApi with
    target := X86_64.target
    doc := Spec.MlDsa.power2RoundApi.doc
    code := Impl.MlDsa.X86_64.Round.power2Round
    contract := Spec.MlDsa.power2RoundContract X86_64.abi
    verified := power2Round_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.highBitsApi with
    target := X86_64.target
    doc := Spec.MlDsa.highBitsApi.doc
    code := Impl.MlDsa.X86_64.Round.highBits
    contract := Spec.MlDsa.highBitsContract X86_64.abi
    verified := highBits_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.lowBitsApi with
    target := X86_64.target
    doc := Spec.MlDsa.lowBitsApi.doc
    code := Impl.MlDsa.X86_64.Round.lowBits
    contract := Spec.MlDsa.lowBitsContract X86_64.abi
    verified := lowBits_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.highBitsApi with
    name := Spec.MlDsa.highBitsApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlDsa.highBitsApi.doc (notes := ["The function computes on eight coefficients at a time in AVX2 \
      registers, multiplying by shifts and additions; it needs AVX and AVX2."])
    code := Impl.MlDsa.X86_64.Round.highBitsAvx2
    contract := Spec.MlDsa.highBitsContract X86_64.abi
    verified := highBitsY_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  { Spec.MlDsa.lowBitsApi with
    name := Spec.MlDsa.lowBitsApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlDsa.lowBitsApi.doc (notes := ["The function computes on eight coefficients at a time in AVX2 \
      registers, multiplying by shifts and additions; it needs AVX and AVX2."])
    code := Impl.MlDsa.X86_64.Round.lowBitsAvx2
    contract := Spec.MlDsa.lowBitsContract X86_64.abi
    verified := lowBitsY_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  { Spec.MlDsa.normLtApi with
    target := X86_64.target
    doc := Spec.MlDsa.normLtApi.doc
    code := Impl.MlDsa.X86_64.Round.normLt
    contract := Spec.MlDsa.normLtContract X86_64.abi
    verified := normLt_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.makeHintApi with
    target := X86_64.target
    doc := Spec.MlDsa.makeHintApi.doc
    code := Impl.MlDsa.X86_64.Round.makeHint
    contract := Spec.MlDsa.makeHintContract X86_64.abi
    verified := makeHint_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.normLtApi with
    name := Spec.MlDsa.normLtApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlDsa.normLtApi.doc (notes := ["The function compares eight coefficients at a time in AVX2 \
      registers; it needs AVX and AVX2."])
    code := Impl.MlDsa.X86_64.Round.normLtAvx2
    contract := Spec.MlDsa.normLtContract X86_64.abi
    verified := normLtY_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  { Spec.MlDsa.makeHintApi with
    name := Spec.MlDsa.makeHintApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlDsa.makeHintApi.doc (notes := ["The function computes eight hints at a time in AVX2 \
      registers, multiplying by shifts and additions; it needs AVX and AVX2."])
    code := Impl.MlDsa.X86_64.Round.makeHintAvx2
    contract := Spec.MlDsa.makeHintContract X86_64.abi
    verified := makeHintY_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] },
  { Spec.MlDsa.useHintApi with
    target := X86_64.target
    doc := Spec.MlDsa.useHintApi.doc
    code := Impl.MlDsa.X86_64.Round.useHint
    contract := Spec.MlDsa.useHintContract X86_64.abi
    verified := useHint_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.useHintApi with
    name := Spec.MlDsa.useHintApi.name ++ "_avx2"
    target := X86_64.target
    doc := Spec.MlDsa.useHintApi.doc (notes := ["The function computes on eight coefficients at a time in AVX2 \
      registers, multiplying by shifts and additions; it needs AVX and AVX2."])
    code := Impl.MlDsa.X86_64.Round.useHintAvx2
    contract := Spec.MlDsa.useHintContract X86_64.abi
    verified := useHintY_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel)
    features := ["avx", "avx2"] }]

end VG.Artifacts.MlDsaRound.X86_64
