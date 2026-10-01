import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.CmacAes.X86.Verified

/-!
# AES-CMAC (NIST SP 800-38B) on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

Each function calls `vg_aes_ctr32` in a frame that pushes its six stack
arguments, so uses 28 bytes of stack with the return address.
-/

namespace VG.Artifacts.CmacAes.X86

open VG.Proof.CmacAes.X86

/-- How the functions encrypt a block. -/
def ctrNote : String := "This implementation encrypts each block with `vg_aes_ctr32`."

def artifacts : List Artifact := [
  { Spec.Cmac.aesSubkeysApi with
    target := X86.target
    doc := Spec.Cmac.aesSubkeysApi.doc (notes := [ctrNote])
    code := Impl.CmacAes.X86.subkeys
    contract := Spec.Cmac.aesSubkeysContract X86.abi 28
    stack := 28
    verified := subkeys_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Cmac.aesUpdateApi with
    target := X86.target
    doc := Spec.Cmac.aesUpdateApi.doc (notes := [ctrNote])
    code := Impl.CmacAes.X86.update
    contract := Spec.Cmac.aesUpdateContract X86.abi 28
    stack := 28
    verified := update_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Cmac.aesFinalizeApi with
    target := X86.target
    doc := Spec.Cmac.aesFinalizeApi.doc (notes := [ctrNote])
    code := Impl.CmacAes.X86.finalize
    contract := Spec.Cmac.aesFinalizeContract X86.abi 28
    stack := 28
    verified := finalize_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.CmacAes.X86
