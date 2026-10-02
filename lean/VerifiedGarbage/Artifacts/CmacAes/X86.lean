import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.CmacAes.X86.Verified
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Verified

/-!
# AES-CMAC (NIST SP 800-38B) on x86

Each function calls `vg_aes_ctr32` in a frame that pushes its six stack
arguments, so uses 28 bytes of stack with the return address. The streaming
functions (`init`, `absorb`, `finish`) call those in frames of their four
or six arguments, so use 48 (`init`) or 56 bytes of stack.
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
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Cmac.aesInitApi with
    target := X86.target
    doc := Spec.Cmac.aesInitApi.doc (notes := [
      "This implementation expands the key with `vg_aes_expand_key` and derives the subkeys with \
        `vg_cmac_aes_subkeys`."])
    code := Impl.CmacAes.Stream.X86.init
    contract := Spec.Cmac.aesInitContract X86.abi 48
    stack := 48
    verified := Proof.CmacAes.Stream.X86.init_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Cmac.aesAbsorbApi with
    target := X86.target
    doc := Spec.Cmac.aesAbsorbApi.doc (notes := [
      "This implementation chains the blocks with `vg_cmac_aes_update`."])
    code := Impl.CmacAes.Stream.X86.absorb
    contract := Spec.Cmac.aesAbsorbContract X86.abi 56
    stack := 56
    verified := Proof.CmacAes.Stream.X86.absorb_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Cmac.aesFinishApi with
    target := X86.target
    doc := Spec.Cmac.aesFinishApi.doc (notes := [
      "This implementation computes the MAC with `vg_cmac_aes_finalize`."])
    code := Impl.CmacAes.Stream.X86.finish
    contract := Spec.Cmac.aesFinishContract X86.abi 56
    stack := 56
    verified := Proof.CmacAes.Stream.X86.finish_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.CmacAes.X86
