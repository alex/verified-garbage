import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Aes.AArch64.Shared

/-!
# AES on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Aes.AArch64

def artifacts : List Artifact := [
  { Spec.Aes.expandKeyApi with
    target := AArch64.target
    doc := Spec.Aes.expandKeyApi.doc
      (notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.AArch64.expandKey
    contract := Spec.Aes.expandKeyContract AArch64.abi
    verified := Proof.Aes.AArch64.Shared.expandKey
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Gcm.ctr32Api with
    target := AArch64.target
    doc := Spec.Gcm.ctr32Api.doc
      (notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.AArch64.ctr32
    contract := Spec.Gcm.ctr32Contract AArch64.abi
    verified := Proof.Aes.AArch64.Shared.ctr32
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Aes.AArch64
