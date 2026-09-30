import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.X25519.X86
import VerifiedGarbage.Proof.X25519.X86.Verified
import VerifiedGarbage.Proof.X25519.X86.Lit

/-!
# X25519 (RFC 7748) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.X25519.X86

def artifacts : List Artifact := [
  { Spec.X25519.x25519Api with
    target := X86.target
    doc := Spec.X25519.x25519Api.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are eight 32-bit words, multiplied by product scanning \
      and reduced with `2^256 = 38` (mod p); the inversion is ref10's addition chain."])
    code := Impl.X25519.X86.x25519
    contract := Spec.X25519.x25519Contract X86.abi
    verified := Proof.X25519.X86.x25519_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.X25519.X86
