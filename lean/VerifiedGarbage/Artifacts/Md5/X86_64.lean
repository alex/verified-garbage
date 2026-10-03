import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Md5.X86_64.Shared
import VerifiedGarbage.Proof.Md5.X86_64.Avx512.Lit

/-! # MD5 (RFC 1321) on x86-64 -/

namespace VG.Artifacts.Md5.X86_64

def artifacts : List Artifact := [
  { Spec.Md5.compressApi with
    target := X86_64.target
    doc := Spec.Md5.compressApi.doc
    code := Impl.Md5.X86_64.compress
    contract := Spec.Md5.compressContract X86_64.abi
    verified := Proof.Md5.X86_64.Shared.compress
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Md5.initApi with
    target := X86_64.target
    doc := Spec.Md5.initApi.doc
    code := Impl.Md5.X86_64.Stream.init
    contract := Spec.Md5.initContract X86_64.abi
    verified := Proof.Md5.X86_64.Shared.init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Md5.compressApi with
    name := Spec.Md5.compressApi.name ++ "_avx512"
    target := X86_64.target
    doc := Spec.Md5.compressApi.doc
      (notes := ["Uses AVX-512 on `xmm` registers: `vpternlogd` for the auxiliary functions and `vprold`."])
    code := Impl.Md5.X86_64.Avx512.compress
    contract := Spec.Md5.compressContract X86_64.abi
    verified := Proof.Md5.X86_64.Shared.compress_avx512
    features := ["avx", "avx512f", "avx512vl"]
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Md5.X86_64
