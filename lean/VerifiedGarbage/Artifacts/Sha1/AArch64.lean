import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha1.AArch64.Shared
import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Compress

/-!
# SHA-1 (FIPS 180-4) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Sha1.AArch64

def artifacts : List Artifact := [
  { Spec.Sha1.compressApi with
    target := AArch64.target
    doc := Spec.Sha1.compressApi.doc
    code := Impl.Sha1.AArch64.compress
    contract := Spec.Sha1.compressContract AArch64.abi
    verified := Proof.Sha1.AArch64.Shared.compress
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha1.initApi with
    target := AArch64.target
    doc := Spec.Sha1.initApi.doc
    code := Impl.Sha1.AArch64.Stream.init
    contract := Spec.Sha1.initContract AArch64.abi
    verified := Proof.Sha1.AArch64.Shared.init
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Sha1.compressApi with
    name := "vg_sha1_compress_sha2"
    target := AArch64.target
    doc := Spec.Sha1.compressApi.doc (notes := ["Uses the AArch64 SHA-1 instructions."])
    code := Impl.Sha1.AArch64.Sha2.compress
    contract := Spec.Sha1.compressContract AArch64.abi
    verified := Proof.Sha1.AArch64.Shared.compress_of Proof.Sha1.AArch64.Sha2.compress_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := ["sha2"] }]

end VG.Artifacts.Sha1.AArch64
