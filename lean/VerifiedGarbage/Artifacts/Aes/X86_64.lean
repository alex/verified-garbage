import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey

/-!
# AES on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

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
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Aes.X86_64
