import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Verified

/-!
# ML-DSA (FIPS 204) signing on 32-bit ARM

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaSign.Arm

open VG
open VG.Proof.MlDsa.Arm.Sign (prims)

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves `r4`–`r11` and its return address in `scratch`; its calls use the 28 \
    bytes of stack below the stack pointer (the calls with a fifth argument push it there).",
   "The signing loop runs at most 814 iterations (FIPS 204 Appendix C). Each iteration computes \
    every validity check and combines them without branching: the one branch on their result \
    is the only place an iteration's outcome affects timing."]

def artifacts : List Artifact := [
  { Spec.MlDsa.sign44Api with
    target := Arm.target
    doc := Spec.MlDsa.sign44Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa44
    contract := Spec.MlDsa.signContract Spec.MlDsa.mlDsa44 Arm.abi 28
    stack := 28
    verified := Proof.MlDsa.Arm.Sign.sign44_verified'
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.sign65Api with
    target := Arm.target
    doc := Spec.MlDsa.sign65Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa65
    contract := Spec.MlDsa.signContract Spec.MlDsa.mlDsa65 Arm.abi 28
    stack := 28
    verified := Proof.MlDsa.Arm.Sign.sign65_verified'
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.sign87Api with
    target := Arm.target
    doc := Spec.MlDsa.sign87Api.doc (notes := notes)
    code := Impl.MlDsa.Arm.Sign.sign prims Spec.MlDsa.mlDsa87
    contract := Spec.MlDsa.signContract Spec.MlDsa.mlDsa87 Arm.abi 28
    stack := 28
    verified := Proof.MlDsa.Arm.Sign.sign87_verified'
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaSign.Arm
