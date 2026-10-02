import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Aes.X86.ExpandKey

/-! # AES on x86 -/

namespace VG.Artifacts.Aes.X86

def artifacts : List Artifact := [
  { Spec.Aes.expandKeyApi with
    target := X86.target
    doc := Spec.Aes.expandKeyApi.doc
      (notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.X86.expandKey
    contract := Spec.Aes.expandKeyContract X86.abi
    verified := Proof.Aes.X86.expandKey_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.ctr32Api with
    target := X86.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Constant-time bitsliced AES, two blocks at a time, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.X86.ctr32
    contract := Spec.Gcm.ctr32Contract X86.abi
    verified := Proof.Aes.X86.ctr32_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Aes.X86
