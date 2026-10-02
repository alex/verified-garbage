import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.CmacAes.X86_64.Verified
import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Verified

/-!
# AES-CMAC (NIST SP 800-38B) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_ctr32`, are emitted once for each implementation
(`Variants/AesCtr32/X86_64/`), named with its suffix (e.g.
`vg_cmac_aes_update_aesni`), and need its CPU features.

The stack is 8 bytes for every implementation of the first three: the
return address of the call of `vg_aes_ctr32`, which makes no calls. The
streaming functions (`init`, `absorb`, `finish`) call those, so their stack
is 16 bytes; `init` also calls the implementation of `vg_aes_expand_key`
that goes with `v`.
-/

namespace VG.Generic.AesCtr32.X86_64.CmacAes

open VG.Proof.CmacAes.X86_64

/-- Which implementation of `vg_aes_ctr32` an instance calls. -/
def ctrNote (v : Proof.Aes.X86_64.Ctr32Impl) : String :=
  "This implementation encrypts each block with `" ++ v.callee.name ++ "`."

/-- Which CMAC functions an instance of a streaming function calls. -/
def streamNote (v : Proof.Aes.X86_64.Ctr32Impl) : String :=
  "This implementation calls the CMAC functions made with `" ++ v.callee.name ++ "` (e.g. `" ++
    Spec.Cmac.aesUpdateApi.name ++ v.suffix ++ "`)."

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
    features := v.features },
  { Spec.Cmac.aesInitApi with
    name := Spec.Cmac.aesInitApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Cmac.aesInitApi.doc (notes := [streamNote v,
      "It expands the key with `" ++ v.expand.name ++ "`."])
    code := Impl.CmacAes.Stream.X86_64.init v.expand v.callee v.suffix
    contract := Spec.Cmac.aesInitContract X86_64.abi 16
    stack := 16
    verified := Proof.CmacAes.Stream.X86_64.init_verified v
    spSafe := Proof.CmacAes.Stream.X86_64.init_spSafe v
    features := v.features },
  { Spec.Cmac.aesAbsorbApi with
    name := Spec.Cmac.aesAbsorbApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Cmac.aesAbsorbApi.doc (notes := [streamNote v])
    code := Impl.CmacAes.Stream.X86_64.absorb v.callee v.suffix
    contract := Spec.Cmac.aesAbsorbContract X86_64.abi 16
    stack := 16
    verified := Proof.CmacAes.Stream.X86_64.absorb_verified v
    spSafe := Proof.CmacAes.Stream.X86_64.absorb_spSafe v
    features := v.features },
  { Spec.Cmac.aesFinishApi with
    name := Spec.Cmac.aesFinishApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.Cmac.aesFinishApi.doc (notes := [streamNote v])
    code := Impl.CmacAes.Stream.X86_64.finish v.callee v.suffix
    contract := Spec.Cmac.aesFinishContract X86_64.abi 16
    stack := 16
    verified := Proof.CmacAes.Stream.X86_64.finish_verified v
    spSafe := Proof.CmacAes.Stream.X86_64.finish_spSafe v
    features := v.features }]

end VG.Generic.AesCtr32.X86_64.CmacAes
