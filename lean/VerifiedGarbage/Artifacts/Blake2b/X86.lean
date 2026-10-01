import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Blake2.X86.CompressB.Verified

/-!
# BLAKE2b (RFC 7693) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Blake2b.X86

def artifacts : List Artifact := [
  { Spec.Blake2.compressBApi with
    target := X86.target
    doc := Spec.Blake2.compressBApi.doc
    code := Impl.Blake2.X86.CompressB.compress
    contract := Spec.Blake2.compressBContract X86.abi
    verified := Proof.Blake2.X86.CompressB.compressB_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Blake2b.X86
