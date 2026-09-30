import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Inst

/-!
# ML-DSA (FIPS 204) verification on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaVerify.AArch64

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `x24`–`x28` and `x30` in `scratch`, and uses no stack of its \
    own; the functions it calls use the 16 bytes of stack below the stack pointer.",
   "It calls the `vg_mldsa_*` primitives and the SHAKE256 sponge. The samplers' results are combined \
    without a branch, so the only branches depend on the public key and the signature."]

def artifacts : List Artifact := [
  { Spec.MlDsa.verify44Api with
    target := AArch64.target
    doc := Spec.MlDsa.verify44Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.KeyGen.verify44
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Verify.verify44_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.verify65Api with
    target := AArch64.target
    doc := Spec.MlDsa.verify65Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.KeyGen.verify65
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Verify.verify65_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.verify87Api with
    target := AArch64.target
    doc := Spec.MlDsa.verify87Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.KeyGen.verify87
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.Verify.verify87_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaVerify.AArch64
