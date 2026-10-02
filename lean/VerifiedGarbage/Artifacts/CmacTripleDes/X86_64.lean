import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Verified

/-!
# TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on x86-64

The functions call nothing and use no stack.
-/

namespace VG.Artifacts.CmacTripleDes.X86_64

open VG.Proof.CmacTripleDes.X86_64

/-- How the functions compute DES. -/
def desNote : String :=
  "This implementation computes DES without tables: its bit permutations as shifts and masks, \
  and its eight S-boxes at once, bitsliced across a 64-bit word, as a tree of multiplexers \
  over constants."

def artifacts : List Artifact := [
  { Spec.Cmac.tdesInitApi with
    target := X86_64.target
    doc := Spec.Cmac.tdesInitApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.X86_64.init
    contract := Spec.Cmac.tdesInitContract X86_64.abi 0
    verified := init_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Cmac.tdesUpdateApi with
    target := X86_64.target
    doc := Spec.Cmac.tdesUpdateApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.X86_64.update
    contract := Spec.Cmac.tdesUpdateContract X86_64.abi 0
    verified := update_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Cmac.tdesFinalizeApi with
    target := X86_64.target
    doc := Spec.Cmac.tdesFinalizeApi.doc (notes := [desNote])
    code := Impl.CmacTripleDes.X86_64.finalize
    contract := Spec.Cmac.tdesFinalizeContract X86_64.abi 0
    verified := finalize_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.CmacTripleDes.X86_64
