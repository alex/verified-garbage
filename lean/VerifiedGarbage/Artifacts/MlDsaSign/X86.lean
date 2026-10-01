import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.MlDsa.X86.Sign.Verified

/-!
# ML-DSA (FIPS 204) signing on x86

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.

Each function saves its caller's registers in a frame of 16 bytes below the
return address, and calls the primitives with their arguments pushed below
it: at most 5 arguments and the return address (24 bytes), and the 56 bytes
the samplers use (`stack := 96`).
-/

namespace VG.Artifacts.MlDsaSign.X86

open VG.Proof.MlDsa.X86.Sign (prims)

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function keeps its working space, `Â`, `ŝ₁`, `ŝ₂`, `t̂₀` and the polynomials of each iteration \
    in `scratch`, and calls the ML-DSA primitives (`vg_mldsa_*`) and the Keccak functions.",
   "The signing loop runs at most 814 iterations (FIPS 204 Appendix C). Each iteration computes \
    every validity check and combines them without branching: the one branch on their result \
    is the only place an iteration's outcome affects timing."]

def artifacts : List Artifact := [
  { Spec.MlDsa.sign44Api with
    target := X86.target
    doc := Spec.MlDsa.sign44Api.doc (notes := notes)
    code := Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa44
    contract := Spec.MlDsa.signContract Spec.MlDsa.mlDsa44 X86.abi 96
    stack := 96
    verified := Proof.MlDsa.X86.Sign.sign44_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.sign65Api with
    target := X86.target
    doc := Spec.MlDsa.sign65Api.doc (notes := notes)
    code := Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa65
    contract := Spec.MlDsa.signContract Spec.MlDsa.mlDsa65 X86.abi 96
    stack := 96
    verified := Proof.MlDsa.X86.Sign.sign65_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { Spec.MlDsa.sign87Api with
    target := X86.target
    doc := Spec.MlDsa.sign87Api.doc (notes := notes)
    code := Impl.MlDsa.X86.Sign.sign prims Spec.MlDsa.mlDsa87
    contract := Spec.MlDsa.signContract Spec.MlDsa.mlDsa87 X86.abi 96
    stack := 96
    verified := Proof.MlDsa.X86.Sign.sign87_verified
    spSafe := Code.all_of_allInstrs (by decide +kernel) }]

end VG.Artifacts.MlDsaSign.X86
