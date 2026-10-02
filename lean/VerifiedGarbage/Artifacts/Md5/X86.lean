import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Md5.X86.Shared

/-! # MD5 (RFC 1321) on x86 -/

namespace VG.Artifacts.Md5.X86

def artifacts : List Artifact := [
  { Spec.Md5.compressApi with
    target := X86.target
    doc := Spec.Md5.compressApi.doc
    code := Impl.Md5.X86.compress
    contract := Spec.Md5.compressContract X86.abi
    verified := Proof.Md5.X86.Shared.compress
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Md5.initApi with
    target := X86.target
    doc := Spec.Md5.initApi.doc
    code := Impl.Md5.X86.Stream.init
    contract := Spec.Md5.initContract X86.abi
    verified := Proof.Md5.X86.Shared.init
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Md5.updateApi with
    target := X86.target
    doc := Spec.Md5.updateApi.doc
    code := Impl.Md5.X86.Stream.update
    contract := Spec.Md5.updateContract X86.abi 20
    stack := 20
    verified := Proof.Md5.X86.Shared.update
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Md5.finalizeApi with
    target := X86.target
    doc := Spec.Md5.finalizeApi.doc
    code := Impl.Md5.X86.Stream.finalize
    contract := Spec.Md5.finalizeContract X86.abi 20
    stack := 20
    verified := Proof.Md5.X86.Shared.finalize
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Md5.X86
