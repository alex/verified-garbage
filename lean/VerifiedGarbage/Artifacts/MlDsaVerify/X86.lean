import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Inst

/-!
# ML-DSA (FIPS 204) verification on x86 (32-bit)

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

The functions save their caller's registers in a frame of 16 bytes below
the return address; their calls of the primitives use the 80 bytes below
it: at most 5 arguments, the return address and the primitive's 56 bytes
(`stack := 96`).
-/

namespace VG.Artifacts.MlDsaVerify.X86

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers in a frame of 16 bytes; its calls use \
    the 80 bytes of stack below it.",
   "It returns early only when the hint is malformed or `z` is out of bounds, which depend on the \
    signature alone. It samples every polynomial of `A` and `c` whatever the samplers return, \
    zeroing the output of a sampler that fails rather than branching on it, and compares `c~` \
    with the recomputed value without branching on the bytes."]

def artifacts : List Artifact := [
  { Spec.MlDsa.verify44Api with
    target := X86.target
    doc := Spec.MlDsa.verify44Api.doc (notes := notes)
    code := Impl.MlDsa.X86.Verify.verify44
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 X86.abi 96
    stack := 96
    verified := Proof.MlDsa.X86.Verify.verify44_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.verify65Api with
    target := X86.target
    doc := Spec.MlDsa.verify65Api.doc (notes := notes)
    code := Impl.MlDsa.X86.Verify.verify65
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 X86.abi 96
    stack := 96
    verified := Proof.MlDsa.X86.Verify.verify65_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.verify87Api with
    target := X86.target
    doc := Spec.MlDsa.verify87Api.doc (notes := notes)
    code := Impl.MlDsa.X86.Verify.verify87
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 X86.abi 96
    stack := 96
    verified := Proof.MlDsa.X86.Verify.verify87_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlDsaVerify.X86
