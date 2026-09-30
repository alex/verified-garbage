import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Inst

/-!
# ML-DSA (FIPS 204) key generation on x86-64

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaKeyGen.X86_64

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers in `scratch`; its calls use the 32 \
    bytes of stack below its return address.",
   "It samples every polynomial of `A` and of `s1` and `s2` whatever the samplers return, and \
    zeroes the polynomial of a sampler that fails rather than branching on it: its timing does not \
    depend on whether key generation fails."]

def artifacts : List Artifact := [
  { Spec.MlDsa.keyGen44Api with
    target := X86_64.target
    doc := Spec.MlDsa.keyGen44Api.doc (notes := notes)
    code := Impl.MlDsa.X86_64.KeyGen.keyGen44
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 X86_64.abi 32
    stack := 32
    verified := Proof.MlDsa.X86_64.KeyGen.keyGen44_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.keyGen65Api with
    target := X86_64.target
    doc := Spec.MlDsa.keyGen65Api.doc (notes := notes)
    code := Impl.MlDsa.X86_64.KeyGen.keyGen65
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 X86_64.abi 32
    stack := 32
    verified := Proof.MlDsa.X86_64.KeyGen.keyGen65_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.keyGen87Api with
    target := X86_64.target
    doc := Spec.MlDsa.keyGen87Api.doc (notes := notes)
    code := Impl.MlDsa.X86_64.KeyGen.keyGen87
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 X86_64.abi 32
    stack := 32
    verified := Proof.MlDsa.X86_64.KeyGen.keyGen87_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlDsaKeyGen.X86_64
