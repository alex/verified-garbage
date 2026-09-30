import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Inst

/-!
# ML-DSA (FIPS 204) verification on 32-bit ARM

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaVerify.Arm

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers and `lr` in `scratch`; the functions it \
    calls use the 36 bytes of stack below the stack pointer.",
   "It calls the `vg_mldsa_*` primitives and the SHAKE256 sponge. The samplers' results and the \
    comparison of the commitment hash are combined without a branch, so the only branches depend \
    on the signature (whether its hint is well formed and its `z` small enough)."]

def artifacts : List Artifact := [
  { Spec.MlDsa.verify44Api with
    target := Arm.target
    doc := Spec.MlDsa.verify44Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.Verify.verify44
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 Arm.abi 36
    stack := 36
    verified := Proof.MlDsa.Arm.Verify.verify44_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.verify65Api with
    target := Arm.target
    doc := Spec.MlDsa.verify65Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.Verify.verify65
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 Arm.abi 36
    stack := 36
    verified := Proof.MlDsa.Arm.Verify.verify65_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.verify87Api with
    target := Arm.target
    doc := Spec.MlDsa.verify87Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.Verify.verify87
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 Arm.abi 36
    stack := 36
    verified := Proof.MlDsa.Arm.Verify.verify87_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaVerify.Arm
