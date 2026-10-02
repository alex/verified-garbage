import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.MlDsa.X86.Message.Verified

/-!
# ML-DSA (FIPS 204) on x86 (32-bit): signing messages

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

The function saves its caller's registers in a frame of 16 bytes below the
return address; below that, its calls push at most 5 arguments and the return
address, and the signing function on `μ` uses 96 bytes
(`stack := 16 + 20 + 4 + 96 = 136`).
-/

namespace VG.Artifacts.MlDsaSignMessage.X86

open VG

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers in a frame of 16 bytes, and keeps the \
    address of the last 1 KiB of `scratch` in `esi`. It computes the message representative with \
    the SHAKE256 sponge (`vg_keccak_absorb`, `vg_keccak_pad`, `vg_keccak_squeeze`) in that 1 KiB, \
    and calls the signing function on it, which uses the rest of `scratch`."]

def artifacts : List Artifact := [
  { Spec.MlDsa.signMessage44Api with
    target := X86.target
    doc := Spec.MlDsa.signMessage44Api.doc (notes := notes)
    code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign44Api.name
      (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    contract := Spec.MlDsa.signMessageContract Spec.MlDsa.mlDsa44 X86.abi 136
    stack := 136
    verified := Proof.MlDsa.X86.Message.signMessage44_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.signMessage65Api with
    target := X86.target
    doc := Spec.MlDsa.signMessage65Api.doc (notes := notes)
    code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign65Api.name
      (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    contract := Spec.MlDsa.signMessageContract Spec.MlDsa.mlDsa65 X86.abi 136
    stack := 136
    verified := Proof.MlDsa.X86.Message.signMessage65_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.signMessage87Api with
    target := X86.target
    doc := Spec.MlDsa.signMessage87Api.doc (notes := notes)
    code := Impl.MlDsa.X86.Message.signMessage Spec.MlDsa.sign87Api.name
      (Impl.MlDsa.X86.Sign.sign Proof.MlDsa.X86.Sign.prims Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    contract := Spec.MlDsa.signMessageContract Spec.MlDsa.mlDsa87 X86.abi 136
    stack := 136
    verified := Proof.MlDsa.X86.Message.signMessage87_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlDsaSignMessage.X86
