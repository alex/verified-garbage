import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.X25519.AArch64.Word
import VerifiedGarbage.Proof.X25519.AArch64.Word.Verified

/-!
# X25519 (RFC 7748) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.X25519.AArch64

def artifacts : List Artifact := [
  { Spec.X25519.x25519Api with
    target := AArch64.target
    doc := Spec.X25519.x25519Api.doc (notes := ["The function saves the callee-saved registers \
      it uses (`x19`–`x24`) in `scratch`. Field elements use four 64-bit words with \
      `mul`/`umulh`, dedicated squaring, and reduction modulo 2^255 - 19. The inversion \
      uses the ref10 addition chain (254 squarings and 11 multiplications)."])
    code := Impl.X25519.AArch64.Word.x25519
    contract := Spec.X25519.x25519Contract AArch64.abi
    verified := Proof.X25519.AArch64.Word.x25519_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.X25519.AArch64
