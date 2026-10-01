import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.CmacAes.X86_64.Verified

/-!
# AES-CMAC (NIST SP 800-38B) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_ctr32`, are emitted once for each
implementation (`Variants/AesCtr32/X86_64/`), named with its suffix (e.g.
`vg_cmac_aes_update_aesni`), and need its CPU features. **Review note**:
`sig` and `doc` are trusted, as they tie the Rust caller to the contract;
check them against the contract's `pre`/`post`. An artifact made from a
function's `Api` (in `Spec/`, reviewed with the contract) takes them from
there, and this file adds only notes on the implementation. The emitter adds
the `# Safety` items that depend on the target (`Sig.layoutDoc`), from
`stack` and `writeArgs`, which `ofSig` checks against the contract.

The stack is 8 bytes for every implementation: the return address of the
call of `vg_aes_ctr32`, which makes no calls.
-/

namespace VG.Generic.AesCtr32.X86_64.CmacAes

open VG.Proof.CmacAes.X86_64

/-- Which implementation of `vg_aes_ctr32` an instance calls. -/
def ctrNote (v : Proof.Aes.X86_64.Ctr32Impl) : String :=
  "This implementation encrypts each block with `" ++ v.callee.name ++ "`."

def artifacts (v : Proof.Aes.X86_64.Ctr32Impl) : List Artifact := [
  { Spec.Cmac.aesSubkeysApi with
    name := Spec.Cmac.aesSubkeysApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Cmac.aesSubkeysApi.doc (notes := [ctrNote v])
    code := Impl.CmacAes.X86_64.subkeys v.callee
    contract := Spec.Cmac.aesSubkeysContract X86_64.abi 8
    stack := 8
    verified := subkeys_verified v
    spSafe := subkeys_spSafe v
    features := v.features },
  { Spec.Cmac.aesUpdateApi with
    name := Spec.Cmac.aesUpdateApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Cmac.aesUpdateApi.doc (notes := [ctrNote v])
    code := Impl.CmacAes.X86_64.update v.callee
    contract := Spec.Cmac.aesUpdateContract X86_64.abi 8
    stack := 8
    verified := update_verified v
    spSafe := update_spSafe v
    features := v.features },
  { Spec.Cmac.aesFinalizeApi with
    name := Spec.Cmac.aesFinalizeApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Cmac.aesFinalizeApi.doc (notes := [ctrNote v])
    code := Impl.CmacAes.X86_64.finalize v.callee
    contract := Spec.Cmac.aesFinalizeContract X86_64.abi 8
    stack := 8
    verified := finalize_verified v
    spSafe := finalize_spSafe v
    features := v.features }]

end VG.Generic.AesCtr32.X86_64.CmacAes
