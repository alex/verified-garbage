import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.Scrypt.X86.Salsa
import VerifiedGarbage.Impl.Scrypt.X86.BlockMix
import VerifiedGarbage.Impl.Scrypt.X86.RoMix
import VerifiedGarbage.Proof.Scrypt.X86.BlockMixVerified
import VerifiedGarbage.Proof.Scrypt.X86.RoMixCT
import VerifiedGarbage.Proof.Scrypt.X86.Salsa

/-!
# scrypt (RFC 7914): Salsa20/8, scryptBlockMix and scryptROMix on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Scrypt.X86

def artifacts : List Artifact := [
  { Spec.Scrypt.salsaApi with
    target := X86.target
    doc := Spec.Scrypt.salsaApi.doc
    code := Impl.Scrypt.X86.salsa
    contract := Spec.Scrypt.salsaContract X86.abi
    verified := Proof.Scrypt.X86.salsa_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Scrypt.blockMixApi with
    target := X86.target
    doc := Spec.Scrypt.blockMixApi.doc
    code := Impl.Scrypt.X86.blockMix
    contract := Spec.Scrypt.blockMixContract X86.abi 12
    stack := 12
    verified := Proof.Scrypt.X86.BlockMix.blockMix_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.Scrypt.roMixApi with
    target := X86.target
    doc := Spec.Scrypt.roMixApi.doc
    code := Impl.Scrypt.X86.roMix
    contract := Spec.Scrypt.roMixContract X86.abi 36
    stack := 36
    verified := Proof.Scrypt.X86.RoMix.roMix_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.Scrypt.X86
