import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.CmacAes.AArch64.Verified
import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Verified

/-!
# AES-CMAC (NIST SP 800-38B) on AArch64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_ctr32`, are emitted once for each implementation
(`Variants/AesCtr32/AArch64/`), named with its suffix (e.g.
`vg_cmac_aes_update_aes`), and need its CPU features.

The functions use no stack: their calls (`bl`) keep the return address in
`x30`, which they save in the scratch buffer. The streaming functions
(`init`, `absorb`, `finish`) call the first three; `init` also calls the
implementation of `vg_aes_expand_key` that goes with `v`.
-/

namespace VG.Generic.AesCtr32.AArch64.CmacAes

open VG.Proof.CmacAes.AArch64

/-- Which implementation of `vg_aes_ctr32` an instance calls. -/
def ctrNote (v : Proof.Aes.AArch64.Ctr32Impl) : String :=
  "This implementation encrypts each block with `" ++ v.callee.name ++ "`."

/-- Which CMAC functions an instance of a streaming function calls. -/
def streamNote (v : Proof.Aes.AArch64.Ctr32Impl) : String :=
  "This implementation calls the CMAC functions made with `" ++ v.callee.name ++ "` (e.g. `" ++
    Spec.Cmac.aesUpdateApi.name ++ v.suffix ++ "`)."

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
    features := v.features },
  { Spec.Cmac.aesInitApi with
    name := Spec.Cmac.aesInitApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Cmac.aesInitApi.doc (notes := [streamNote v,
      "It expands the key with `" ++ v.expand.name ++ "`."])
    code := Impl.CmacAes.Stream.AArch64.init v.expand v.callee v.suffix
    contract := Spec.Cmac.aesInitContract AArch64.abi
    verified := Proof.CmacAes.Stream.AArch64.init_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.Cmac.aesAbsorbApi with
    name := Spec.Cmac.aesAbsorbApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Cmac.aesAbsorbApi.doc (notes := [streamNote v])
    code := Impl.CmacAes.Stream.AArch64.absorb v.callee v.suffix
    contract := Spec.Cmac.aesAbsorbContract AArch64.abi
    verified := Proof.CmacAes.Stream.AArch64.absorb_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features },
  { Spec.Cmac.aesFinishApi with
    name := Spec.Cmac.aesFinishApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Cmac.aesFinishApi.doc (notes := [streamNote v])
    code := Impl.CmacAes.Stream.AArch64.finish v.callee v.suffix
    contract := Spec.Cmac.aesFinishContract AArch64.abi
    verified := Proof.CmacAes.Stream.AArch64.finish_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.AesCtr32.AArch64.CmacAes
