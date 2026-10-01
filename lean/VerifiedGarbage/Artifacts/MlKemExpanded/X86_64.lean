import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.EcXVerified
import VerifiedGarbage.Proof.MlKem.X86_64.DcXVerified

/-!
# ML-KEM-768 (FIPS 203) on x86-64: encapsulation and decapsulation with expanded keys

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract. The functions that sample `Â` (`keygen_expanded`,
`expand_ek`) are in `Generic/MlKemSample4/X86_64/MlKem768.lean`.
-/

namespace VG.Artifacts.MlKemExpanded.X86_64

/-- The notes of the functions here. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers in `scratch`; its calls use the 32 bytes of \
    stack below its return address."]

def artifacts : List Artifact := [
  { Spec.MlKem.encapsExpandedApi with
    target := X86_64.target
    doc := Spec.MlKem.encapsExpandedApi.doc (notes := notes)
    code := Impl.MlKem.X86_64.encapsX
    contract := Spec.MlKem.encapsExpandedContract X86_64.abi 32
    stack := 32
    verified := Proof.MlKem.X86_64.encapsX_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlKem.decapsExpandedApi with
    target := X86_64.target
    doc := Spec.MlKem.decapsExpandedApi.doc (notes := notes)
    code := Impl.MlKem.X86_64.decapsX
    contract := Spec.MlKem.decapsExpandedContract X86_64.abi 32
    stack := 32
    verified := Proof.MlKem.X86_64.decapsX_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlKemExpanded.X86_64
