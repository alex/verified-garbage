import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.AesGcm.X86_64.Verified

/-!
# AES-GCM (NIST SP 800-38D) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_expand_key`, `vg_aes_ctr32` and `vg_ghash`,
are emitted once for each combination (`Variants/AesGcm/X86_64/`), named with
its suffix (e.g. `vg_aes_gcm_seal_aesni_pclmul`), and need its CPU features.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; these artifacts are made from each function's `Api` (in
`Spec/`, reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

The stack is 8 bytes for every function: the return address of a call of
`vg_aes_expand_key`, `vg_aes_ctr32` or `vg_ghash`, which make no calls.
-/

namespace VG.Generic.AesGcm.X86_64.AesGcm

open VG.Proof.AesGcm.X86_64

/-- Which implementations an instance calls. -/
def note (v : GcmImpl) : String :=
  "This implementation encrypts with `" ++ v.ctr.callee.name ++ "` (and expands keys with `" ++
    v.key.fn.name ++ "`) and hashes with `" ++ v.gh.fn.name ++ "`."

def artifacts (v : GcmImpl) : List Artifact := [
  { Spec.Gcm.initApi with
    name := Spec.Gcm.initApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.initApi.doc (notes := [note v])
    code := Impl.AesGcm.X86_64.init v.callees
    contract := Spec.Gcm.initContract X86_64.abi 8
    stack := 8
    verified := init_verified v
    spSafe := init_spSafe v
    features := v.features },
  { Spec.Gcm.sealApi with
    name := Spec.Gcm.sealApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.sealApi.doc (notes := [note v])
    code := Impl.AesGcm.X86_64.«seal» v.callees
    contract := Spec.Gcm.sealContract X86_64.abi 8
    stack := 8
    verified := seal_verified v
    spSafe := seal_spSafe v
    features := v.features },
  { Spec.Gcm.openApi with
    name := Spec.Gcm.openApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.openApi.doc (notes := [note v])
    code := Impl.AesGcm.X86_64.«open» v.callees
    contract := Spec.Gcm.openContract X86_64.abi 8
    stack := 8
    verified := open_verified v
    spSafe := open_spSafe v
    features := v.features },
  { Spec.Gcm.streamInitApi with
    name := Spec.Gcm.streamInitApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamInitApi.doc (notes := [note v])
    code := Impl.AesGcm.X86_64.streamInit v.callees
    contract := Spec.Gcm.streamInitContract X86_64.abi 8
    stack := 8
    verified := streamInit_verified v
    spSafe := streamInit_spSafe v
    features := v.features },
  { Spec.Gcm.streamAadApi with
    name := Spec.Gcm.streamAadApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamAadApi.doc (notes := [note v])
    code := Impl.AesGcm.X86_64.streamAad v.callees
    contract := Spec.Gcm.streamAadContract X86_64.abi 8
    stack := 8
    verified := streamAad_verified v
    spSafe := streamAad_spSafe v
    features := v.features },
  { Spec.Gcm.streamEncryptApi with
    name := Spec.Gcm.streamEncryptApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamEncryptApi.doc (notes := [note v])
    code := Impl.AesGcm.X86_64.streamEncrypt v.callees
    contract := Spec.Gcm.streamEncryptContract X86_64.abi 8
    stack := 8
    verified := streamEncrypt_verified v
    spSafe := streamEncrypt_spSafe v
    features := v.features },
  { Spec.Gcm.streamDecryptApi with
    name := Spec.Gcm.streamDecryptApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamDecryptApi.doc (notes := [note v])
    code := Impl.AesGcm.X86_64.streamDecrypt v.callees
    contract := Spec.Gcm.streamDecryptContract X86_64.abi 8
    stack := 8
    verified := streamDecrypt_verified v
    spSafe := streamDecrypt_spSafe v
    features := v.features },
  { Spec.Gcm.streamFinishApi with
    name := Spec.Gcm.streamFinishApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamFinishApi.doc (notes := [note v])
    code := Impl.AesGcm.X86_64.streamFinish v.callees
    contract := Spec.Gcm.streamFinishContract X86_64.abi 8
    stack := 8
    verified := streamFinish_verified v
    spSafe := streamFinish_spSafe v
    features := v.features },
  { Spec.Gcm.streamVerifyApi with
    name := Spec.Gcm.streamVerifyApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Gcm.streamVerifyApi.doc (notes := [note v])
    code := Impl.AesGcm.X86_64.streamVerify v.callees
    contract := Spec.Gcm.streamVerifyContract X86_64.abi 8
    stack := 8
    verified := streamVerify_verified v
    spSafe := streamVerify_spSafe v
    features := v.features }]

end VG.Generic.AesGcm.X86_64.AesGcm
