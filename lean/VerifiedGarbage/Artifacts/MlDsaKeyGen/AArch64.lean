import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst

/-!
# ML-DSA (FIPS 204) key generation on AArch64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaKeyGen.AArch64

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `x24`–`x28` and `x30` in `scratch`, and uses no stack of its \
    own; the functions it calls use the 16 bytes of stack below the stack pointer.",
   "It samples every polynomial of `A` and of `s1` and `s2` whatever the samplers return, and \
    zeroes the polynomial of a sampler that fails rather than branching on it: its timing does not \
    depend on whether key generation fails."]

def artifacts : List Artifact := [
  { Spec.MlDsa.keyGen44Api with
    target := AArch64.target
    doc := Spec.MlDsa.keyGen44Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.KeyGen.keyGen44
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.keyGen44_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.keyGen65Api with
    target := AArch64.target
    doc := Spec.MlDsa.keyGen65Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.KeyGen.keyGen65
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.keyGen65_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.keyGen87Api with
    target := AArch64.target
    doc := Spec.MlDsa.keyGen87Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.KeyGen.keyGen87
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 AArch64.abi 16
    stack := 16
    verified := Proof.MlDsa.AArch64.KeyGen.keyGen87_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.MlDsaKeyGen.AArch64
