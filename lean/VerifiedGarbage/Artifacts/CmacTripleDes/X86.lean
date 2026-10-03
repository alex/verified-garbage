import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.CmacTripleDes.X86.Verified

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

The functions call nothing and use no stack: they save our caller's
registers in the scratch buffer, and reload their stack arguments.
-/

namespace VG.Artifacts.CmacTripleDes.X86

open VG.Proof.CmacTripleDes.X86

/-- How the functions compute DES. -/
def desNote : String :=
  "This implementation computes DES without tables: its bit permutations as shifts and masks, \
  and its eight S-boxes at once, bitsliced across 32-bit words, as a tree of multiplexers \
  over constants."

def artifacts : List Artifact := [
  { Spec.Cmac.tdesInitApi with
    target := X86.target
    doc := Spec.Cmac.tdesInitApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.X86.init
    contract := Spec.Cmac.tdesInitContract X86.abi 0
    verified := init_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Cmac.tdesUpdateApi with
    target := X86.target
    doc := Spec.Cmac.tdesUpdateApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.X86.update
    contract := Spec.Cmac.tdesUpdateContract X86.abi 0
    verified := update_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Cmac.tdesFinalizeApi with
    target := X86.target
    doc := Spec.Cmac.tdesFinalizeApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.X86.finalize
    contract := Spec.Cmac.tdesFinalizeContract X86.abi 0
    verified := finalize_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.CmacTripleDes.X86
