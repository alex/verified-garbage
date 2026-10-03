import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack

/-! # ML-DSA (FIPS 204) on x86-64: the encodings -/

namespace VG.Artifacts.MlDsaPack.X86_64

def artifacts : List Artifact := [
  { Spec.MlDsa.simpleBitPackApi with
    target := X86_64.target
    doc := Spec.MlDsa.simpleBitPackApi.doc
    code := Impl.MlDsa.X86_64.Pack.simpleBitPack
    contract := Spec.MlDsa.simpleBitPackContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Pack.simpleBitPack_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.bitPackApi with
    target := X86_64.target
    doc := Spec.MlDsa.bitPackApi.doc
    code := Impl.MlDsa.X86_64.Pack.bitPack
    contract := Spec.MlDsa.bitPackContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Pack.bitPack_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.bitUnpackApi with
    target := X86_64.target
    doc := Spec.MlDsa.bitUnpackApi.doc
    code := Impl.MlDsa.X86_64.Pack.bitUnpack
    contract := Spec.MlDsa.bitUnpackContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Pack.bitUnpack_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.unpackT1Api with
    target := X86_64.target
    doc := Spec.MlDsa.unpackT1Api.doc
    code := Impl.MlDsa.X86_64.Pack.unpackT1
    contract := Spec.MlDsa.unpackT1Contract X86_64.abi
    verified := Proof.MlDsa.X86_64.Pack.unpackT1_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.hintBitPackApi with
    target := X86_64.target
    doc := Spec.MlDsa.hintBitPackApi.doc
    code := Impl.MlDsa.X86_64.Pack.hintBitPack
    contract := Spec.MlDsa.hintBitPackContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Pack.hintBitPack_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.hintBitUnpackApi with
    target := X86_64.target
    doc := Spec.MlDsa.hintBitUnpackApi.doc
    code := Impl.MlDsa.X86_64.Pack.hintBitUnpack
    contract := Spec.MlDsa.hintBitUnpackContract X86_64.abi
    verified := Proof.MlDsa.X86_64.Pack.hintBitUnpack_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlDsaPack.X86_64
