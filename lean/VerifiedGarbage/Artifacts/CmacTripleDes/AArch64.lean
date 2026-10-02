import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Verified

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

The functions call nothing and use no stack: the return address stays in `x30`.
-/

namespace VG.Artifacts.CmacTripleDes.AArch64

open VG.Proof.CmacTripleDes.AArch64

/-- How the functions compute DES. -/
def desNote : String :=
  "This implementation computes DES without tables: its bit permutations as shifts and masks, \
  and its eight S-boxes at once, bitsliced across a 64-bit word, as a tree of multiplexers \
  over constants."

def artifacts : List Artifact := [
  { Spec.Cmac.tdesInitApi with
    target := AArch64.target
    doc := Spec.Cmac.tdesInitApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.AArch64.init
    contract := Spec.Cmac.tdesInitContract AArch64.abi 0
    verified := init_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.tdesUpdateApi with
    target := AArch64.target
    doc := Spec.Cmac.tdesUpdateApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.AArch64.update
    contract := Spec.Cmac.tdesUpdateContract AArch64.abi 0
    verified := update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.tdesFinalizeApi with
    target := AArch64.target
    doc := Spec.Cmac.tdesFinalizeApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.AArch64.finalize
    contract := Spec.Cmac.tdesFinalizeContract AArch64.abi 0
    verified := finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.CmacTripleDes.AArch64
