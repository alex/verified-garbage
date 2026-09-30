import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims

/-!
# ML-DSA (FIPS 204) on x86-64: verification

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

The stack is 24 bytes: the return address of a call of a primitive, and up
to 16 bytes for its own calls.
-/

namespace VG.Artifacts.MlDsaVerify.X86_64

open VG
open VG.Proof.MlDsa.X86_64.Verify (prims prims_ok verify_prims verify_spSafe)

/-- What the documentation says of the implementation. -/
def note : String :=
  "It calls the `vg_mldsa_*` primitives and the SHAKE256 sponge. The samplers' results are combined \
  without a branch, so the only branches depend on the public key and the signature."

def artifacts : List Artifact := [
  { Spec.MlDsa.verify44Api with
    target := X86_64.target
    doc := Spec.MlDsa.verify44Api.doc (notes := [note])
    code := Impl.MlDsa.X86_64.Verify.verify prims Spec.MlDsa.mlDsa44
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 X86_64.abi 24
    stack := 24
    verified := verify_prims (List.mem_cons_self ..)
    spSafe := verify_spSafe prims_ok (List.mem_cons_self ..) },
  { Spec.MlDsa.verify65Api with
    target := X86_64.target
    doc := Spec.MlDsa.verify65Api.doc (notes := [note])
    code := Impl.MlDsa.X86_64.Verify.verify prims Spec.MlDsa.mlDsa65
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 X86_64.abi 24
    stack := 24
    verified := verify_prims (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := verify_spSafe prims_ok (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  { Spec.MlDsa.verify87Api with
    target := X86_64.target
    doc := Spec.MlDsa.verify87Api.doc (notes := [note])
    code := Impl.MlDsa.X86_64.Verify.verify prims Spec.MlDsa.mlDsa87
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 X86_64.abi 24
    stack := 24
    verified := verify_prims (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := verify_spSafe prims_ok (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) }]

end VG.Artifacts.MlDsaVerify.X86_64
