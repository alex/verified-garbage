import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.AesGcm.X86.Verified

/-!
# AES-GCM (NIST SP 800-38D) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_ctr32` with its `vg_aes_expand_key` and of
`vg_ghash`, are emitted once for each combination (`Variants/AesGcm/X86/`),
named with its suffix (e.g. `vg_aes_gcm_seal_aesni_pclmul`), and need its CPU
features: `init` only AES's, `stream_init` and `stream_aad` only GHASH's.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller
to the contract; check them against the contract's `pre`/`post`. An
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

namespace VG.Generic.AesGcm.X86.AesGcm

open VG.Proof.AesGcm.X86

/-- How the functions are built, and which implementations they call. -/
def callNote (v : GcmImpl) : String :=
  "This implementation calls `" ++ v.ctr.callee.name ++ "`, `" ++ v.gh.fn.name ++ "` and `" ++
    v.ctr.expand.name ++ "` for the block cipher, GHASH and the key schedule, with the arguments it \
    keeps in the working space."

def artifacts (v : GcmImpl) : List Artifact := [
  { Spec.Gcm.initApi with
    name := Spec.Gcm.initApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Gcm.initApi.doc (notes := [callNote v])
    code := Impl.AesGcm.X86.init v.callees
    contract := Spec.Gcm.initContract X86.abi 28
    stack := 28
    verified := init_verified (vg := v)
    spSafe := init_spSafe v
    features := (v.ctr.features) },
  { Spec.Gcm.streamAadApi with
    name := Spec.Gcm.streamAadApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Gcm.streamAadApi.doc (notes := [callNote v])
    code := Impl.AesGcm.X86.streamAad v.callees
    contract := Spec.Gcm.streamAadContract X86.abi 24
    stack := 24
    verified := streamAad_verified (vg := v)
    spSafe := streamAad_spSafe v
    features := v.gh.features },
  { Spec.Gcm.streamInitApi with
    name := Spec.Gcm.streamInitApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Gcm.streamInitApi.doc (notes := [callNote v])
    code := Impl.AesGcm.X86.streamInit v.callees
    contract := Spec.Gcm.streamInitContract X86.abi 24
    stack := 24
    verified := streamInit_verified (vg := v)
    spSafe := streamInit_spSafe v
    features := v.gh.features },
  { Spec.Gcm.streamEncryptApi with
    name := Spec.Gcm.streamEncryptApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Gcm.streamEncryptApi.doc (notes := [callNote v])
    code := Impl.AesGcm.X86.streamEncrypt v.callees
    contract := Spec.Gcm.streamEncryptContract X86.abi 28
    stack := 28
    verified := streamEncrypt_verified (vg := v)
    spSafe := streamEncrypt_spSafe v
    features := v.features },
  { Spec.Gcm.streamDecryptApi with
    name := Spec.Gcm.streamDecryptApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Gcm.streamDecryptApi.doc (notes := [callNote v])
    code := Impl.AesGcm.X86.streamDecrypt v.callees
    contract := Spec.Gcm.streamDecryptContract X86.abi 28
    stack := 28
    verified := streamDecrypt_verified (vg := v)
    spSafe := streamDecrypt_spSafe v
    features := v.features },
  { Spec.Gcm.streamFinishApi with
    name := Spec.Gcm.streamFinishApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Gcm.streamFinishApi.doc (notes := [callNote v])
    code := Impl.AesGcm.X86.streamFinish v.callees
    contract := Spec.Gcm.streamFinishContract X86.abi 28
    stack := 28
    verified := streamFinish_verified (vg := v)
    spSafe := streamFinish_spSafe v
    features := v.features },
  { Spec.Gcm.streamVerifyApi with
    name := Spec.Gcm.streamVerifyApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Gcm.streamVerifyApi.doc (notes := [callNote v])
    code := Impl.AesGcm.X86.streamVerify v.callees
    contract := Spec.Gcm.streamVerifyContract X86.abi 28
    stack := 28
    verified := streamVerify_verified (vg := v)
    spSafe := streamVerify_spSafe v
    features := v.features },
  { Spec.Gcm.sealApi with
    name := Spec.Gcm.sealApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Gcm.sealApi.doc (notes := [callNote v])
    code := Impl.AesGcm.X86.«seal» v.callees
    contract := Spec.Gcm.sealContract X86.abi 28
    stack := 28
    verified := seal_verified (vg := v)
    spSafe := seal_spSafe v
    features := v.features },
  { Spec.Gcm.openApi with
    name := Spec.Gcm.openApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Gcm.openApi.doc (notes := [callNote v])
    code := Impl.AesGcm.X86.«open» v.callees
    contract := Spec.Gcm.openContract X86.abi 28
    stack := 28
    verified := open_verified (vg := v)
    spSafe := open_spSafe v
    features := v.features }]

end VG.Generic.AesGcm.X86.AesGcm
