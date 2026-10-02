import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.AesGcm.AArch64.Verified

/-!
# AES-GCM (NIST SP 800-38D) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_expand_key`, `vg_aes_ctr32` and `vg_ghash`,
are emitted once for each combination (`Variants/AesGcm/AArch64/`), named with
its suffix (e.g. `vg_aes_gcm_seal_aes_pmull`), and need its CPU features.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; these artifacts are made from each function's `Api` (in
`Spec/`, reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

Each function needs the CPU features of the implementations it calls:
`init` calls only AES's, `stream_init` and `stream_aad` only GHASH's.

The functions use no stack: their calls (`bl`) keep the return address in
`x30`, which they save in the scratch buffer. `seal` and `open` read their
last arguments from the stack.
-/

namespace VG.Generic.AesGcm.AArch64.AesGcm

open VG.Proof.AesGcm.AArch64

/-- Which implementations an instance calls. -/
def note (v : GcmImpl) : String :=
  "This implementation encrypts with `" ++ v.ctr.callee.name ++ "` (and expands keys with `" ++
    v.key.fn.name ++ "`) and hashes with `" ++ v.gh.fn.name ++ "`."

def artifacts (v : GcmImpl) : List Artifact := [
  { Spec.Gcm.initApi with
    name := Spec.Gcm.initApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Gcm.initApi.doc (notes := [note v])
    code := Impl.AesGcm.AArch64.init v.callees
    contract := Spec.Gcm.initContract AArch64.abi
    verified := init_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.ctr.features },
  { Spec.Gcm.sealApi with
    name := Spec.Gcm.sealApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Gcm.sealApi.doc (notes := [note v])
    code := Impl.AesGcm.AArch64.«seal» v.callees
    contract := Spec.Gcm.sealContract AArch64.abi
    verified := seal_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.Gcm.openApi with
    name := Spec.Gcm.openApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Gcm.openApi.doc (notes := [note v])
    code := Impl.AesGcm.AArch64.«open» v.callees
    contract := Spec.Gcm.openContract AArch64.abi
    verified := open_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.Gcm.streamInitApi with
    name := Spec.Gcm.streamInitApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Gcm.streamInitApi.doc (notes := [note v])
    code := Impl.AesGcm.AArch64.streamInit v.callees
    contract := Spec.Gcm.streamInitContract AArch64.abi
    verified := streamInit_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.gh.features },
  { Spec.Gcm.streamAadApi with
    name := Spec.Gcm.streamAadApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Gcm.streamAadApi.doc (notes := [note v])
    code := Impl.AesGcm.AArch64.streamAad v.callees
    contract := Spec.Gcm.streamAadContract AArch64.abi
    verified := streamAad_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.gh.features },
  { Spec.Gcm.streamEncryptApi with
    name := Spec.Gcm.streamEncryptApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Gcm.streamEncryptApi.doc (notes := [note v])
    code := Impl.AesGcm.AArch64.streamEncrypt v.callees
    contract := Spec.Gcm.streamEncryptContract AArch64.abi
    verified := streamEncrypt_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.Gcm.streamDecryptApi with
    name := Spec.Gcm.streamDecryptApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Gcm.streamDecryptApi.doc (notes := [note v])
    code := Impl.AesGcm.AArch64.streamDecrypt v.callees
    contract := Spec.Gcm.streamDecryptContract AArch64.abi
    verified := streamDecrypt_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.Gcm.streamFinishApi with
    name := Spec.Gcm.streamFinishApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Gcm.streamFinishApi.doc (notes := [note v])
    code := Impl.AesGcm.AArch64.streamFinish v.callees
    contract := Spec.Gcm.streamFinishContract AArch64.abi
    verified := streamFinish_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.Gcm.streamVerifyApi with
    name := Spec.Gcm.streamVerifyApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Gcm.streamVerifyApi.doc (notes := [note v])
    code := Impl.AesGcm.AArch64.streamVerify v.callees
    contract := Spec.Gcm.streamVerifyContract AArch64.abi
    verified := streamVerify_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.AesGcm.AArch64.AesGcm
