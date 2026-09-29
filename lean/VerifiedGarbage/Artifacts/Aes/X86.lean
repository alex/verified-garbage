import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Aes.X86.ExpandKey

/-!
# AES on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

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
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Gcm.ctr32Api with
    target := X86.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Constant-time bitsliced AES, two blocks at a time, in the style of BearSSL's \
        `aes_ct` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.X86.ctr32
    contract := Spec.Gcm.ctr32Contract X86.abi
    verified := Proof.Aes.X86.ctr32_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Aes.X86
