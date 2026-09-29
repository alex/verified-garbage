import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash

/-!
# GHASH on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Gcm.AArch64

def artifacts : List Artifact := [
  { Spec.Gcm.ghashApi with
    target := AArch64.target
    doc := Spec.Gcm.ghashApi.doc
      (notes := ["`•` is computed bit by bit as Algorithm 1 of §6.3 does, with masks instead of \
        branches."])
    code := Impl.Gcm.AArch64.ghash
    contract := Spec.Gcm.ghashContract AArch64.abi
    verified := Proof.Gcm.AArch64.ghash_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Gcm.AArch64
