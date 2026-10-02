import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.Scrypt.Arm.Salsa
import VerifiedGarbage.Impl.Scrypt.Arm.BlockMix
import VerifiedGarbage.Impl.Scrypt.Arm.RoMix
import VerifiedGarbage.Proof.Scrypt.Arm.BlockMixVerified
import VerifiedGarbage.Proof.Scrypt.Arm.RoMixCT
import VerifiedGarbage.Proof.Scrypt.Arm.Lit
import VerifiedGarbage.Proof.Scrypt.Arm.Whole.Verified

/-!
# scrypt (RFC 7914): Salsa20/8, scryptBlockMix, scryptROMix and scrypt on 32-bit ARM

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

`vg_scrypt` calls `vg_pbkdf2_hmac_sha256` (registered in
`Artifacts/Pbkdf2Sha256/Arm.lean`), the one implementation of PBKDF2-HMAC-SHA256
on this target, and `vg_scrypt_romix`. Its `stack` is the 40 bytes the frame
of PBKDF2's stack arguments and PBKDF2's own frames use.
-/

namespace VG.Artifacts.Scrypt.Arm

def artifacts : List Artifact := [
  { Spec.Scrypt.salsaApi with
    target := Arm.target
    doc := Spec.Scrypt.salsaApi.doc
    code := Impl.Scrypt.Arm.salsa
    contract := Spec.Scrypt.salsaContract Arm.abi
    verified := Proof.Scrypt.Arm.salsa_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Scrypt.blockMixApi with
    target := Arm.target
    doc := Spec.Scrypt.blockMixApi.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := Impl.Scrypt.Arm.blockMix
    contract := Spec.Scrypt.blockMixContract Arm.abi
    verified := Proof.Scrypt.Arm.BlockMix.blockMix_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Scrypt.roMixApi with
    target := Arm.target
    doc := Spec.Scrypt.roMixApi.doc
      (notes := ["The function uses no stack: it saves its return address in `scratch`."])
    code := Impl.Scrypt.Arm.roMix
    contract := Spec.Scrypt.roMixContract Arm.abi
    verified := Proof.Scrypt.Arm.RoMix.roMix_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Scrypt.scryptApi with
    target := Arm.target
    doc := Spec.Scrypt.scryptApi.doc (notes := ["Derives both keys with `vg_pbkdf2_hmac_sha256` and runs \
      scryptROMix on each block with `vg_scrypt_romix`, using the start of `scratch` as the working \
      space of each. The function has no stack frame of its own: the caller's `r4`–`r11` and the return \
      address are saved in the last of the `r + 16` chunks of `scratch`, which neither callee uses; each \
      call's stack arguments are pushed in a frame of their own."])
    code := Impl.Scrypt.Arm.scrypt Spec.Hmac.sha256I.pbkdf2Api.name Proof.Scrypt.Arm.Whole.pbkC
    contract := Spec.Scrypt.scryptContract Arm.abi 40
    stack := 40
    verified := Proof.Scrypt.Arm.Whole.scrypt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Scrypt.Arm
