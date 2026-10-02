import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Verified

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

The functions call nothing and use no stack: they save our caller's
registers in the scratch buffer, and the return address stays in `lr`.
-/

namespace VG.Artifacts.CmacTripleDes.Arm

open VG.Proof.CmacTripleDes.Arm

/-- How the functions compute DES. -/
def desNote : String :=
  "This implementation computes DES without tables: its bit permutations as shifts and masks, \
  and its eight S-boxes at once, bitsliced across 32-bit words, as a tree of multiplexers \
  over constants."

def artifacts : List Artifact := [
  { Spec.Cmac.tdesInitApi with
    target := Arm.target
    doc := Spec.Cmac.tdesInitApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.Arm.init
    contract := Spec.Cmac.tdesInitContract Arm.abi 0
    verified := init_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.tdesUpdateApi with
    target := Arm.target
    doc := Spec.Cmac.tdesUpdateApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.Arm.update
    contract := Spec.Cmac.tdesUpdateContract Arm.abi 0
    verified := update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.tdesFinalizeApi with
    target := Arm.target
    doc := Spec.Cmac.tdesFinalizeApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.Arm.finalize
    contract := Spec.Cmac.tdesFinalizeContract Arm.abi 0
    verified := finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.CmacTripleDes.Arm
