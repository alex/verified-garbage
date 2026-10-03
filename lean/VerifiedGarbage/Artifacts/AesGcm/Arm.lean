import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.AesGcm.Arm.Verified

/-!
# AES-GCM (NIST SP 800-38D) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

Each function calls `vg_aes_ctr32` or `vg_ghash` in a frame that pushes
their two stack arguments, so uses 8 bytes of stack (`init` also calls
`vg_aes_expand_key`, which takes no stack arguments).
-/

namespace VG.Artifacts.AesGcm.Arm

open VG.Proof.AesGcm.Arm

/-- How `init` is built. -/
def initNote : String := "This implementation calls `vg_aes_expand_key` for the key schedule and \
  `vg_aes_ctr32` to encrypt the zero block into the hash subkey."

/-- How `stream_init` and `stream_aad` are built. -/
def ghashNote : String := "This implementation calls `vg_ghash` for GHASH."

/-- How the other functions are built. -/
def callNote : String := "This implementation calls `vg_aes_ctr32` for the block cipher and `vg_ghash` for GHASH."

def artifacts : List Artifact := [
  { Spec.Gcm.initApi with
    target := Arm.target
    doc := Spec.Gcm.initApi.doc (notes := [initNote])
    code := Impl.AesGcm.Arm.init
    contract := Spec.Gcm.initContract Arm.abi 8
    stack := 8
    verified := init_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Gcm.sealApi with
    target := Arm.target
    doc := Spec.Gcm.sealApi.doc (notes := [callNote])
    code := Impl.AesGcm.Arm.«seal»
    contract := Spec.Gcm.sealContract Arm.abi 8
    stack := 8
    verified := seal_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Gcm.openApi with
    target := Arm.target
    doc := Spec.Gcm.openApi.doc (notes := [callNote])
    code := Impl.AesGcm.Arm.«open»
    contract := Spec.Gcm.openContract Arm.abi 8
    stack := 8
    verified := open_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Gcm.streamInitApi with
    target := Arm.target
    doc := Spec.Gcm.streamInitApi.doc (notes := [ghashNote])
    code := Impl.AesGcm.Arm.streamInit
    contract := Spec.Gcm.streamInitContract Arm.abi 8
    stack := 8
    verified := streamInit_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Gcm.streamAadApi with
    target := Arm.target
    doc := Spec.Gcm.streamAadApi.doc (notes := [ghashNote])
    code := Impl.AesGcm.Arm.streamAad
    contract := Spec.Gcm.streamAadContract Arm.abi 8
    stack := 8
    verified := streamAad_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Gcm.streamEncryptApi with
    target := Arm.target
    doc := Spec.Gcm.streamEncryptApi.doc (notes := [callNote])
    code := Impl.AesGcm.Arm.streamEncrypt
    contract := Spec.Gcm.streamEncryptContract Arm.abi 8
    stack := 8
    verified := streamEncrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Gcm.streamDecryptApi with
    target := Arm.target
    doc := Spec.Gcm.streamDecryptApi.doc (notes := [callNote])
    code := Impl.AesGcm.Arm.streamDecrypt
    contract := Spec.Gcm.streamDecryptContract Arm.abi 8
    stack := 8
    verified := streamDecrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Gcm.streamFinishApi with
    target := Arm.target
    doc := Spec.Gcm.streamFinishApi.doc (notes := [callNote])
    code := Impl.AesGcm.Arm.streamFinish
    contract := Spec.Gcm.streamFinishContract Arm.abi 8
    stack := 8
    verified := streamFinish_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Gcm.streamVerifyApi with
    target := Arm.target
    doc := Spec.Gcm.streamVerifyApi.doc (notes := [callNote])
    code := Impl.AesGcm.Arm.streamVerify
    contract := Spec.Gcm.streamVerifyContract Arm.abi 8
    stack := 8
    verified := streamVerify_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.AesGcm.Arm
