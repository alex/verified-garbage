import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.CmacAes.Arm.Verified
import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Verified

/-!
# AES-CMAC (NIST SP 800-38B) on ARMv7

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

Each function calls `vg_aes_ctr32` in a frame that pushes its two stack
arguments, so uses 8 bytes of stack. The streaming functions call those:
`init` calls `vg_cmac_aes_subkeys` (and `vg_aes_expand_key`, which uses no
stack), so uses 8 bytes; `absorb` and `finish` call `vg_cmac_aes_update`
and `vg_cmac_aes_finalize` in a frame that pushes their two stack arguments,
so use 16.
-/

namespace VG.Artifacts.CmacAes.Arm

open VG.Proof.CmacAes.Arm

/-- How the functions encrypt a block. -/
def ctrNote : String := "This implementation encrypts each block with `vg_aes_ctr32`."

def artifacts : List Artifact := [
  { Spec.Cmac.aesSubkeysApi with
    target := Arm.target
    doc := Spec.Cmac.aesSubkeysApi.doc (notes := [ctrNote])
    code := Impl.CmacAes.Arm.subkeys
    contract := Spec.Cmac.aesSubkeysContract Arm.abi 8
    stack := 8
    verified := subkeys_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.aesUpdateApi with
    target := Arm.target
    doc := Spec.Cmac.aesUpdateApi.doc (notes := [ctrNote])
    code := Impl.CmacAes.Arm.update
    contract := Spec.Cmac.aesUpdateContract Arm.abi 8
    stack := 8
    verified := update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.aesFinalizeApi with
    target := Arm.target
    doc := Spec.Cmac.aesFinalizeApi.doc (notes := [ctrNote])
    code := Impl.CmacAes.Arm.finalize
    contract := Spec.Cmac.aesFinalizeContract Arm.abi 8
    stack := 8
    verified := finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.aesInitApi with
    target := Arm.target
    doc := Spec.Cmac.aesInitApi.doc (notes := [
      "This implementation expands the key with `vg_aes_expand_key` and derives the subkeys with \
        `vg_cmac_aes_subkeys`."])
    code := Impl.CmacAes.Stream.Arm.init
    contract := Spec.Cmac.aesInitContract Arm.abi 8
    stack := 8
    verified := Proof.CmacAes.Stream.Arm.init_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.aesAbsorbApi with
    target := Arm.target
    doc := Spec.Cmac.aesAbsorbApi.doc (notes := [
      "This implementation chains the blocks with `vg_cmac_aes_update`."])
    code := Impl.CmacAes.Stream.Arm.absorb
    contract := Spec.Cmac.aesAbsorbContract Arm.abi 16
    stack := 16
    verified := Proof.CmacAes.Stream.Arm.absorb_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Cmac.aesFinishApi with
    target := Arm.target
    doc := Spec.Cmac.aesFinishApi.doc (notes := [
      "This implementation computes the MAC with `vg_cmac_aes_finalize`."])
    code := Impl.CmacAes.Stream.Arm.finish
    contract := Spec.Cmac.aesFinishContract Arm.abi 16
    stack := 16
    verified := Proof.CmacAes.Stream.Arm.finish_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.CmacAes.Arm
