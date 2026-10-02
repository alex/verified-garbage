import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.CmacAes.X86.Verified
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Verified

/-!
# AES-CMAC (NIST SP 800-38B) on x86

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling an
implementation `v` of `vg_aes_ctr32`, are emitted once for each implementation
(`Variants/AesCtr32/X86/`), named with its suffix (e.g.
`vg_cmac_aes_update_aesni`), and need its CPU features.

The stack is 28 bytes for the first three functions: their six AES arguments
and the return address. Streaming `init` uses 48 bytes; `absorb` and
`finish` use 56 bytes; `init` also calls the implementation of `vg_aes_expand_key`
that goes with `v`.
-/

namespace VG.Generic.AesCtr32.X86.CmacAes

open VG.Proof.CmacAes.X86

/-- Which implementation of `vg_aes_ctr32` an instance calls. -/
def ctrNote (v : Proof.Aes.X86.Ctr32Impl) : String :=
  "This implementation encrypts each block with `" ++ v.callee.name ++ "`."

/-- Which CMAC functions an instance of a streaming function calls. -/
def streamNote (v : Proof.Aes.X86.Ctr32Impl) : String :=
  "This implementation calls the CMAC functions made with `" ++ v.callee.name ++ "` (e.g. `" ++
    Spec.Cmac.aesUpdateApi.name ++ v.suffix ++ "`)."

def artifacts (v : Proof.Aes.X86.Ctr32Impl) : List Artifact := [
  { Spec.Cmac.aesSubkeysApi with
    name := Spec.Cmac.aesSubkeysApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Cmac.aesSubkeysApi.doc (notes := [ctrNote v])
    code := Impl.CmacAes.X86.subkeys v.callee
    contract := Spec.Cmac.aesSubkeysContract X86.abi 28
    stack := 28
    verified := subkeys_verified v
    spSafe := subkeys_spSafe v
    features := v.features },
  { Spec.Cmac.aesUpdateApi with
    name := Spec.Cmac.aesUpdateApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Cmac.aesUpdateApi.doc (notes := [ctrNote v])
    code := Impl.CmacAes.X86.update v.callee
    contract := Spec.Cmac.aesUpdateContract X86.abi 28
    stack := 28
    verified := update_verified v
    spSafe := update_spSafe v
    features := v.features },
  { Spec.Cmac.aesFinalizeApi with
    name := Spec.Cmac.aesFinalizeApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Cmac.aesFinalizeApi.doc (notes := [ctrNote v])
    code := Impl.CmacAes.X86.finalize v.callee
    contract := Spec.Cmac.aesFinalizeContract X86.abi 28
    stack := 28
    verified := finalize_verified v
    spSafe := finalize_spSafe v
    features := v.features },
  { Spec.Cmac.aesInitApi with
    name := Spec.Cmac.aesInitApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Cmac.aesInitApi.doc (notes := [streamNote v,
      "It expands the key with `" ++ v.expand.name ++ "`."])
    code := Impl.CmacAes.Stream.X86.init v.expand v.callee v.suffix
    contract := Spec.Cmac.aesInitContract X86.abi 48
    stack := 48
    verified := Proof.CmacAes.Stream.X86.init_verified v
    spSafe := Proof.CmacAes.Stream.X86.init_spSafe v
    features := v.features },
  { Spec.Cmac.aesAbsorbApi with
    name := Spec.Cmac.aesAbsorbApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Cmac.aesAbsorbApi.doc (notes := [streamNote v])
    code := Impl.CmacAes.Stream.X86.absorb v.callee v.suffix
    contract := Spec.Cmac.aesAbsorbContract X86.abi 56
    stack := 56
    verified := Proof.CmacAes.Stream.X86.absorb_verified v
    spSafe := Proof.CmacAes.Stream.X86.absorb_spSafe v
    features := v.features },
  { Spec.Cmac.aesFinishApi with
    name := Spec.Cmac.aesFinishApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Cmac.aesFinishApi.doc (notes := [streamNote v])
    code := Impl.CmacAes.Stream.X86.finish v.callee v.suffix
    contract := Spec.Cmac.aesFinishContract X86.abi 56
    stack := 56
    verified := Proof.CmacAes.Stream.X86.finish_verified v
    spSafe := Proof.CmacAes.Stream.X86.finish_spSafe v
    features := v.features }]

end VG.Generic.AesCtr32.X86.CmacAes
