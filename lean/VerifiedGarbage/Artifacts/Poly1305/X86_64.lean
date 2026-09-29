import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Poly1305.X86_64
import VerifiedGarbage.Proof.Poly1305.X86_64.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Finalize
import VerifiedGarbage.Proof.Poly1305.X86_64.Init
import VerifiedGarbage.Proof.Poly1305.X86_64.Update
import VerifiedGarbage.Proof.Poly1305.X86_64.Lit

/-!
# Poly1305 (RFC 8439 §2.5) on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Poly1305.X86_64

def artifacts : List Artifact := [
  { Spec.Poly1305.initApi with
    target := X86_64.target
    doc := Spec.Poly1305.initApi.doc
    code := Impl.Poly1305.X86_64.init
    contract := Spec.Poly1305.initContract X86_64.abi
    verified := Proof.Poly1305.X86_64.init_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Poly1305.blocksApi with
    target := X86_64.target
    doc := Spec.Poly1305.blocksApi.doc
    code := Impl.Poly1305.X86_64.blocks
    contract := Spec.Poly1305.blocksContract X86_64.abi
    verified := Proof.Poly1305.X86_64.blocks_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Poly1305.updateApi with
    target := X86_64.target
    doc := Spec.Poly1305.updateApi.doc
    code := Impl.Poly1305.X86_64.update
    contract := Spec.Poly1305.updateContract X86_64.abi
    verified := Proof.Poly1305.X86_64.update_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Poly1305.finalizeApi with
    target := X86_64.target
    doc := Spec.Poly1305.finalizeApi.doc
    code := Impl.Poly1305.X86_64.finalize
    contract := Spec.Poly1305.finalizeContract X86_64.abi
    verified := Proof.Poly1305.X86_64.finalize_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Poly1305.X86_64
