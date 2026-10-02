import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Sha1.X86_64.Shared

/-! # SHA-1 (FIPS 180-4) on x86-64 -/

namespace VG.Artifacts.Sha1.X86_64

def artifacts : List Artifact := [
  { Spec.Sha1.compressApi with
    target := X86_64.target
    doc := Spec.Sha1.compressApi.doc
    code := Impl.Sha1.X86_64.compress
    contract := Spec.Sha1.compressContract X86_64.abi
    verified := Proof.Sha1.X86_64.Shared.compress
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha1.initApi with
    target := X86_64.target
    doc := Spec.Sha1.initApi.doc
    code := Impl.Sha1.X86_64.Stream.init
    contract := Spec.Sha1.initContract X86_64.abi
    verified := Proof.Sha1.X86_64.Shared.init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Sha1.compressApi with
    name := Spec.Sha1.compressApi.name ++ "_shani"
    target := X86_64.target
    doc := Spec.Sha1.compressApi.doc (notes := ["This implementation uses the SHA extensions."])
    code := Impl.Sha1.X86_64.ShaNi.compress
    contract := Spec.Sha1.compressContract X86_64.abi
    verified := Proof.Sha1.X86_64.Shared.compress_shani
    features := ["sha", "ssse3"]
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Sha1.X86_64
