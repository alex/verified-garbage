import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Scrypt.X86_64.Salsa
import VerifiedGarbage.Impl.Scrypt.X86_64.BlockMix
import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix
import VerifiedGarbage.Proof.Scrypt.X86_64.BlockMixCT
import VerifiedGarbage.Proof.Scrypt.X86_64.RoMixCT
import VerifiedGarbage.Proof.Scrypt.X86_64.Salsa
import VerifiedGarbage.Proof.Scrypt.X86_64.Lit

/-!
# scrypt (RFC 7914): Salsa20/8, scryptBlockMix and scryptROMix on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.Scrypt.X86_64

def artifacts : List Artifact := [
  { Spec.Scrypt.salsaApi with
    target := X86_64.target
    doc := Spec.Scrypt.salsaApi.doc
    code := Impl.Scrypt.X86_64.salsa
    contract := Spec.Scrypt.salsaContract X86_64.abi
    verified := Proof.Scrypt.X86_64.salsa_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Scrypt.blockMixApi with
    target := X86_64.target
    doc := Spec.Scrypt.blockMixApi.doc
    code := Impl.Scrypt.X86_64.blockMix
    contract := Spec.Scrypt.blockMixContract X86_64.abi 8
    stack := 8
    verified := Proof.Scrypt.X86_64.BlockMix.blockMix_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Scrypt.roMixApi with
    target := X86_64.target
    doc := Spec.Scrypt.roMixApi.doc
    code := Impl.Scrypt.X86_64.roMix
    contract := Spec.Scrypt.roMixContract X86_64.abi 16
    stack := 16
    verified := Proof.Scrypt.X86_64.RoMix.roMix_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Scrypt.X86_64
