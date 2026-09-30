import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.NttInv

/-!
# ML-DSA (FIPS 204) on AArch64: the arithmetic of polynomials

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaArith.AArch64

def artifacts : List Artifact := [
  { Spec.MlDsa.nttApi with
    target := AArch64.target
    doc := Spec.MlDsa.nttApi.doc
      (notes := ["The function stores a table of the 256 zetas in `scratch`."])
    code := Impl.MlDsa.AArch64.Arith.ntt
    contract := Spec.MlDsa.nttContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Arith.ntt_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    ofSig := ⟨_, _, _, by unfold Spec.MlDsa.nttContract Spec.MlDsa.inPlaceContract; rfl⟩ },
  { Spec.MlDsa.nttInvApi with
    target := AArch64.target
    doc := Spec.MlDsa.nttInvApi.doc
      (notes := ["The function stores a table of the 256 negated zetas in `scratch`."])
    code := Impl.MlDsa.AArch64.Arith.nttInv
    contract := Spec.MlDsa.nttInvContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Arith.nttInv_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _
    ofSig := ⟨_, _, _, by unfold Spec.MlDsa.nttInvContract Spec.MlDsa.inPlaceContract; rfl⟩ },
  { Spec.MlDsa.mulApi with
    target := AArch64.target
    doc := Spec.MlDsa.mulApi.doc
    code := Impl.MlDsa.AArch64.Arith.mul
    contract := Spec.MlDsa.mulContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Arith.mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.mulAddApi with
    target := AArch64.target
    doc := Spec.MlDsa.mulAddApi.doc
    code := Impl.MlDsa.AArch64.Arith.mulAdd
    contract := Spec.MlDsa.mulAddContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Arith.mulAdd_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.addApi with
    target := AArch64.target
    doc := Spec.MlDsa.addApi.doc
    code := Impl.MlDsa.AArch64.Arith.add
    contract := Spec.MlDsa.addContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Arith.add_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.subApi with
    target := AArch64.target
    doc := Spec.MlDsa.subApi.doc
    code := Impl.MlDsa.AArch64.Arith.sub
    contract := Spec.MlDsa.subContract AArch64.abi
    verified := Proof.MlDsa.AArch64.Arith.sub_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaArith.AArch64
