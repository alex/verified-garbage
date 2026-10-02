import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Verified

/-!
# ML-DSA (FIPS 204) on AArch64: verifying messages

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which call
the SHA-3 sponge functions with an implementation `v` of the Keccak
permutation (`Variants/Keccak/AArch64/`), are emitted once for each
implementation, named with its suffix, and need its CPU features.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; check them against the contract's `pre`/`post`. Each artifact
is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`, reviewed
with the contract), and this file adds only notes on the implementation. The
emitter adds the `# Safety` items that depend on the target
(`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Generic.Keccak.AArch64.MlDsaVerifyMessage

open VG
open VG.Proof.MlDsa.AArch64.Message (verifyFn verifyMessage_verified)

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's `x28` and `x30` and its arguments in the last 1 KiB of `scratch`, \
    and uses no stack of its own; the functions it calls use the 16 bytes of stack below the stack \
    pointer. It computes `tr = H(pk, 64)` and then the message representative with the SHAKE256 sponge (`vg_keccak_absorb`, \
    `vg_keccak_pad`, `vg_keccak_squeeze`) in that 1 KiB, and calls the verification function on it, which \
    uses the rest of `scratch`."]

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  { Spec.MlDsa.verifyMessage44Api with
    name := Spec.MlDsa.verifyMessage44Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.verifyMessage44Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.Message.verifyMessage v.callee (Spec.MlDsa.verify44Api.name ++ v.callee.suffix)
      (Impl.MlDsa.AArch64.Verify.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    contract := Spec.MlDsa.verifyMessageContract Spec.MlDsa.mlDsa44 AArch64.abi 16
    stack := 16
    verified := verifyMessage_verified v (verifyFn v (List.mem_cons_self ..)) (List.mem_cons_self ..)
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.verifyMessage65Api with
    name := Spec.MlDsa.verifyMessage65Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.verifyMessage65Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.Message.verifyMessage v.callee (Spec.MlDsa.verify65Api.name ++ v.callee.suffix)
      (Impl.MlDsa.AArch64.Verify.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    contract := Spec.MlDsa.verifyMessageContract Spec.MlDsa.mlDsa65 AArch64.abi 16
    stack := 16
    verified := verifyMessage_verified v (verifyFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.MlDsa.verifyMessage87Api with
    name := Spec.MlDsa.verifyMessage87Api.name ++ v.callee.suffix
    features := v.features
    target := AArch64.target
    doc := Spec.MlDsa.verifyMessage87Api.doc (notes := notes)
    code := Impl.MlDsa.AArch64.Message.verifyMessage v.callee (Spec.MlDsa.verify87Api.name ++ v.callee.suffix)
      (Impl.MlDsa.AArch64.Verify.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    contract := Spec.MlDsa.verifyMessageContract Spec.MlDsa.mlDsa87 AArch64.abi 16
    stack := 16
    verified := verifyMessage_verified v (verifyFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Generic.Keccak.AArch64.MlDsaVerifyMessage
