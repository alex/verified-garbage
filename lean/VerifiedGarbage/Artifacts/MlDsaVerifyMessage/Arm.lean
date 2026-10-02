import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlDsa.Arm.Message.Verified

/-!
# ML-DSA (FIPS 204) on 32-bit ARM: verifying messages

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaVerifyMessage.Arm

open VG

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `r7` and `lr` and its arguments in the last 1 KiB of `scratch` \
    (keeping the caller's `r7` in the first word of `scratch` while it computes that address), and \
    pushes nothing of its own; the functions it calls use the 36 bytes of stack below the \
    stack pointer. It computes the message representative with the SHAKE256 sponge \
    (`vg_keccak_absorb`, `vg_keccak_pad`, `vg_keccak_squeeze`) in that 1 KiB, and calls the \
    verification function on it, which uses the rest of `scratch`."]

def artifacts : List Artifact := [
  { Spec.MlDsa.verifyMessage44Api with
    target := Arm.target
    doc := Spec.MlDsa.verifyMessage44Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.Message.verifyMessage Spec.MlDsa.verify44Api.name
      Impl.MlDsa.Arm.Verify.verify44 Spec.MlDsa.mlDsa44
    contract := Spec.MlDsa.verifyMessageContract Spec.MlDsa.mlDsa44 Arm.abi 36
    stack := 36
    verified := Proof.MlDsa.Arm.Message.verifyMessage_verified Proof.MlDsa.Arm.Message.verify44Fn
      (List.mem_cons_self ..)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.verifyMessage65Api with
    target := Arm.target
    doc := Spec.MlDsa.verifyMessage65Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.Message.verifyMessage Spec.MlDsa.verify65Api.name
      Impl.MlDsa.Arm.Verify.verify65 Spec.MlDsa.mlDsa65
    contract := Spec.MlDsa.verifyMessageContract Spec.MlDsa.mlDsa65 Arm.abi 36
    stack := 36
    verified := Proof.MlDsa.Arm.Message.verifyMessage_verified Proof.MlDsa.Arm.Message.verify65Fn
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.verifyMessage87Api with
    target := Arm.target
    doc := Spec.MlDsa.verifyMessage87Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.Message.verifyMessage Spec.MlDsa.verify87Api.name
      Impl.MlDsa.Arm.Verify.verify87 Spec.MlDsa.mlDsa87
    contract := Spec.MlDsa.verifyMessageContract Spec.MlDsa.mlDsa87 Arm.abi 36
    stack := 36
    verified := Proof.MlDsa.Arm.Message.verifyMessage_verified Proof.MlDsa.Arm.Message.verify87Fn
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaVerifyMessage.Arm
