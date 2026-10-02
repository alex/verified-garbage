import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.AesGcm.X86.Verified

/-!
# AES-GCM (NIST SP 800-38D) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

Each function calls `vg_aes_ctr32` (six stack arguments) or `vg_ghash`
(five) in a frame of its own, so uses 28 bytes of stack with the return
address (24 for `stream_init` and `stream_aad`, which call only
`vg_ghash`).
-/

namespace VG.Artifacts.AesGcm.X86

open VG.Proof.AesGcm.X86

/-- How the functions are built. -/
def callNote : String := "This implementation calls `vg_aes_ctr32`, `vg_ghash` and `vg_aes_expand_key` for the \
  block cipher, GHASH and the key schedule, with the arguments it keeps in the working space."

def artifacts : List Artifact := [
  { Spec.Gcm.initApi with
    target := X86.target
    doc := Spec.Gcm.initApi.doc (notes := [callNote])
    code := Impl.AesGcm.X86.init
    contract := Spec.Gcm.initContract X86.abi 28
    stack := 28
    verified := init_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.streamAadApi with
    target := X86.target
    doc := Spec.Gcm.streamAadApi.doc (notes := [callNote])
    code := Impl.AesGcm.X86.streamAad
    contract := Spec.Gcm.streamAadContract X86.abi 24
    stack := 24
    verified := streamAad_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.streamInitApi with
    target := X86.target
    doc := Spec.Gcm.streamInitApi.doc (notes := [callNote])
    code := Impl.AesGcm.X86.streamInit
    contract := Spec.Gcm.streamInitContract X86.abi 24
    stack := 24
    verified := streamInit_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.streamEncryptApi with
    target := X86.target
    doc := Spec.Gcm.streamEncryptApi.doc (notes := [callNote])
    code := Impl.AesGcm.X86.streamEncrypt
    contract := Spec.Gcm.streamEncryptContract X86.abi 28
    stack := 28
    verified := streamEncrypt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.streamDecryptApi with
    target := X86.target
    doc := Spec.Gcm.streamDecryptApi.doc (notes := [callNote])
    code := Impl.AesGcm.X86.streamDecrypt
    contract := Spec.Gcm.streamDecryptContract X86.abi 28
    stack := 28
    verified := streamDecrypt_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.streamFinishApi with
    target := X86.target
    doc := Spec.Gcm.streamFinishApi.doc (notes := [callNote])
    code := Impl.AesGcm.X86.streamFinish
    contract := Spec.Gcm.streamFinishContract X86.abi 28
    stack := 28
    verified := streamFinish_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.streamVerifyApi with
    target := X86.target
    doc := Spec.Gcm.streamVerifyApi.doc (notes := [callNote])
    code := Impl.AesGcm.X86.streamVerify
    contract := Spec.Gcm.streamVerifyContract X86.abi 28
    stack := 28
    verified := streamVerify_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.sealApi with
    target := X86.target
    doc := Spec.Gcm.sealApi.doc (notes := [callNote])
    code := Impl.AesGcm.X86.«seal»
    contract := Spec.Gcm.sealContract X86.abi 28
    stack := 28
    verified := seal_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Gcm.openApi with
    target := X86.target
    doc := Spec.Gcm.openApi.doc (notes := [callNote])
    code := Impl.AesGcm.X86.«open»
    contract := Spec.Gcm.openContract X86.abi 28
    stack := 28
    verified := open_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.AesGcm.X86
