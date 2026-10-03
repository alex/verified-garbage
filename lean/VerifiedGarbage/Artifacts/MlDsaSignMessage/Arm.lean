import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified

/-!
# ML-DSA (FIPS 204) on 32-bit ARM: signing messages

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaSignMessage.Arm

open VG

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `r7` and `lr` and its arguments in the last 1 KiB of `scratch` \
    (keeping the caller's `r7` in the first word of `scratch` while it computes that address), and \
    pushes nothing of its own but the fifth argument of the signing function on `μ`, with `lr`; the functions it calls use the 36 bytes of stack below the \
    stack pointer. It computes the message representative with the SHAKE256 sponge \
    (`vg_keccak_absorb`, `vg_keccak_pad`, `vg_keccak_squeeze`) in that 1 KiB, and calls the \
    signing function on it, which uses the rest of `scratch`."]

def artifacts : List Artifact := [
  { Spec.MlDsa.signMessage44Api with
    target := Arm.target
    doc := Spec.MlDsa.signMessage44Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.Message.signMessage Spec.MlDsa.sign44Api.name
      (Impl.MlDsa.Arm.Sign.sign Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    contract := Spec.MlDsa.signMessageContract Spec.MlDsa.mlDsa44 Arm.abi 36
    stack := 36
    verified := Proof.MlDsa.Arm.Message.signMessage_verified Proof.MlDsa.Arm.Message.sign44Fn
      (List.mem_cons_self ..)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.signMessage65Api with
    target := Arm.target
    doc := Spec.MlDsa.signMessage65Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.Message.signMessage Spec.MlDsa.sign65Api.name
      (Impl.MlDsa.Arm.Sign.sign Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    contract := Spec.MlDsa.signMessageContract Spec.MlDsa.mlDsa65 Arm.abi 36
    stack := 36
    verified := Proof.MlDsa.Arm.Message.signMessage_verified Proof.MlDsa.Arm.Message.sign65Fn
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.signMessage87Api with
    target := Arm.target
    doc := Spec.MlDsa.signMessage87Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.Message.signMessage Spec.MlDsa.sign87Api.name
      (Impl.MlDsa.Arm.Sign.sign Proof.MlDsa.Arm.Sign.prims Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    contract := Spec.MlDsa.signMessageContract Spec.MlDsa.mlDsa87 Arm.abi 36
    stack := 36
    verified := Proof.MlDsa.Arm.Message.signMessage_verified Proof.MlDsa.Arm.Message.sign87Fn
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaSignMessage.Arm
