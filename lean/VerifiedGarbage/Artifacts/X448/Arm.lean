import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.X448.Arm
import VerifiedGarbage.Proof.X448.Arm.Verified
import VerifiedGarbage.Proof.X448.Arm.Lit

/-!
# X448 (RFC 7748) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.X448.Arm

def artifacts : List Artifact := [
  { Spec.X448.x448Api with
    target := Arm.target
    doc := Spec.X448.x448Api.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are twenty-eight 16-bit limbs, multiplied with `mul` and \
      reduced with `2^448 = 2^224 + 1` (mod p). Inversion uses an addition chain for `p - 2`."])
    code := Impl.X448.Arm.x448
    contract := Spec.X448.x448Contract Arm.abi
    verified := Proof.X448.Arm.x448_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.X448.Arm
