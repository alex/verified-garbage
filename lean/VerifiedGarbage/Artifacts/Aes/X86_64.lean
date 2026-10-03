import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32

/-! # AES on x86-64 -/

namespace VG.Artifacts.Aes.X86_64

def artifacts : List Artifact := [
  { Spec.Aes.expandKeyApi with
    target := X86_64.target
    doc := Spec.Aes.expandKeyApi.doc
      (notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.X86_64.expandKey
    contract := Spec.Aes.expandKeyContract X86_64.abi
    verified := Proof.Aes.X86_64.expandKey_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.ctr32Api with
    target := X86_64.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.X86_64.ctr32
    contract := Spec.Gcm.ctr32Contract X86_64.abi
    verified := Proof.Aes.X86_64.ctr32_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Aes.expandKeyApi with
    name := "vg_aes_expand_key_aesni"
    target := X86_64.target
    doc := Spec.Aes.expandKeyApi.doc
      (notes := ["Uses AES-NI: four words at a time, with AESKEYGENASSIST."])
    code := Impl.Aes.X86_64.AesNi.expandKey
    contract := Spec.Aes.expandKeyContract X86_64.abi
    verified := Proof.Aes.X86_64.AesNi.Key.expandKey_verified
    features := ["aes"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.ctr32Api with
    name := "vg_aes_ctr32_aesni"
    target := X86_64.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Uses AES-NI: eight blocks at a time, then one at a time."])
    code := Impl.Aes.X86_64.AesNi.ctr32
    contract := Spec.Gcm.ctr32Contract X86_64.abi
    verified := Proof.Aes.X86_64.AesNi.ctr32_verified
    features := ["aes", "ssse3"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.ctr32Api with
    name := "vg_aes_ctr32_vaes"
    target := X86_64.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Uses VAES: sixteen blocks at a time, two in each 256-bit register; the \
        blocks left go eight and then one at a time with AES-NI, as in `vg_aes_ctr32_aesni`."])
    code := Impl.Aes.X86_64.Vaes.ctr32
    contract := Spec.Gcm.ctr32Contract X86_64.abi
    verified := Proof.Aes.X86_64.Vaes.ctr32_verified
    features := ["aes", "avx", "avx2", "ssse3", "vaes"]
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Aes.X86_64
