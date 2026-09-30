import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha512.X86_64.Shared

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

`update` and `finalize`, which call the compression function, are emitted
once for each implementation of it, by SHA-512's variants of `MdHash`
(`Variants/MdHash/X86_64/Sha512*.lean`, `Generic/MdHash/X86_64/Stream.lean`).
-/

namespace VG.Artifacts.Sha512.X86_64

def artifacts : List Artifact := [
  { Spec.Sha512.compressApi with
    target := X86_64.target
    doc := Spec.Sha512.compressApi.doc
    code := Impl.Sha512.X86_64.compress
    contract := Spec.Sha512.compressContract X86_64.abi
    verified := Proof.Sha512.X86_64.Shared.compress
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha512.compressApi with
    name := "vg_sha512_compress_avx2"
    target := X86_64.target
    doc := Spec.Sha512.compressApi.doc
      (notes := ["This implementation computes the message schedules of two blocks at a time in \
        the two lanes of the AVX2 registers, and the rounds with BMI1 and BMI2."])
    code := Impl.Sha512.X86_64.Avx2.compress
    contract := Spec.Sha512.compressContract X86_64.abi
    verified := Proof.Sha512.X86_64.Shared.compress_avx2
    features := ["avx", "avx2", "bmi1", "bmi2"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha512.compressApi with
    name := "vg_sha512_compress_shani"
    target := X86_64.target
    doc := Spec.Sha512.compressApi.doc
      (notes := ["This implementation uses the SHA512 extension."])
    code := Impl.Sha512.X86_64.ShaNi.compress
    contract := Spec.Sha512.compressContract X86_64.abi
    verified := Proof.Sha512.X86_64.Shared.compress_shani
    features := ["avx", "avx2", "sha512"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha512.init384Api with
    target := X86_64.target
    doc := Spec.Sha512.init384Api.doc
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_384
    contract := Spec.Sha512.initContract X86_64.abi Spec.Sha512.H0_384
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_384
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha512.init512Api with
    target := X86_64.target
    doc := Spec.Sha512.init512Api.doc
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512
    contract := Spec.Sha512.initContract X86_64.abi Spec.Sha512.H0_512
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_512
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha512.init512_224Api with
    target := X86_64.target
    doc := Spec.Sha512.init512_224Api.doc
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_224
    contract := Spec.Sha512.initContract X86_64.abi Spec.Sha512.H0_512_224
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_512_224
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha512.init512_256Api with
    target := X86_64.target
    doc := Spec.Sha512.init512_256Api.doc
    code := Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512_256
    contract := Spec.Sha512.initContract X86_64.abi Spec.Sha512.H0_512_256
    verified := Proof.Sha512.X86_64.Shared.init Spec.Sha512.H0_512_256
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sha512.X86_64
