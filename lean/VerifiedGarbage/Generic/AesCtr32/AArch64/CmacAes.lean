import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.CmacAes.AArch64.Verified

/-!
# AES-CMAC (NIST SP 800-38B) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_ctr32`, are emitted once for each implementation
(`Variants/AesCtr32/AArch64/`), named with its suffix (e.g.
`vg_cmac_aes_update_aes`), and need its CPU features.

The functions use no stack: their calls (`bl`) keep the return address in
`x30`, which they save in the scratch buffer.
-/

namespace VG.Generic.AesCtr32.AArch64.CmacAes

open VG.Proof.CmacAes.AArch64

/-- Which implementation of `vg_aes_ctr32` an instance calls. -/
def ctrNote (v : Proof.Aes.AArch64.Ctr32Impl) : String :=
  "This implementation encrypts each block with `" ++ v.callee.name ++ "`."

def artifacts (v : Proof.Aes.AArch64.Ctr32Impl) : List Artifact := [
  { Spec.Cmac.aesSubkeysApi with
    name := Spec.Cmac.aesSubkeysApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Cmac.aesSubkeysApi.doc (notes := [ctrNote v])
    code := Impl.CmacAes.AArch64.subkeys v.callee
    contract := Spec.Cmac.aesSubkeysContract AArch64.abi
    verified := subkeys_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.Cmac.aesUpdateApi with
    name := Spec.Cmac.aesUpdateApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Cmac.aesUpdateApi.doc (notes := [ctrNote v])
    code := Impl.CmacAes.AArch64.update v.callee
    contract := Spec.Cmac.aesUpdateContract AArch64.abi
    verified := update_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.Cmac.aesFinalizeApi with
    name := Spec.Cmac.aesFinalizeApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Cmac.aesFinalizeApi.doc (notes := [ctrNote v])
    code := Impl.CmacAes.AArch64.finalize v.callee
    contract := Spec.Cmac.aesFinalizeContract AArch64.abi
    verified := finalize_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.AesCtr32.AArch64.CmacAes
