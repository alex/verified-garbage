import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Aes.AArch64.Shared

/-!
# AES on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes its signature and most of its `doc` from there: what this
file adds is the `# Safety` items that depend on the target, and any notes.
-/

namespace VG.Artifacts.Aes.AArch64

def artifacts : List Artifact := [
  { Spec.Aes.expandKeyApi with
    target := AArch64.target
    doc := Spec.Aes.expandKeyApi.doc ["`key`, `schedule` and `scratch` must not overlap each \
      other, and no region may wrap around the end of the address space (distinct Rust objects \
      never do)."]
      (notes := ["`SUBWORD` uses a constant-time bitsliced S-box, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.AArch64.expandKey
    contract := Spec.Aes.expandKeyContract AArch64.abi
    verified := Proof.Aes.AArch64.Shared.expandKey
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Gcm.ctr32Api with
    target := AArch64.target
    doc := Spec.Gcm.ctr32Api.doc ["`counter`, `data` and `scratch` must not overlap each other or \
      `schedule`, and no region may wrap around the end of the address space (distinct Rust \
      objects never do)."]
      (notes := ["Constant-time bitsliced AES, four blocks at a time, in the style of BearSSL's \
        `aes_ct64` (Thomas Pornin, MIT licence)."])
    code := Impl.Aes.AArch64.ctr32
    contract := Spec.Gcm.ctr32Contract AArch64.abi
    verified := Proof.Aes.AArch64.Shared.ctr32
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Aes.AArch64
