import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT

/-!
# ML-DSA (FIPS 204) on x86-64: the sampling primitives

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. **Review note**: `sig` and `doc` are trusted, as they tie the Rust
caller to the contract; check them against the contract's `pre`/`post`. Each
artifact is made from its function's `Api` (in `Spec/MlDsa/Poly.lean`,
reviewed with the contract), and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Artifacts.MlDsaSample.X86_64

open VG

def artifacts : List Artifact := [
  { Spec.MlDsa.rejNTTApi with
    target := X86_64.target
    doc := Spec.MlDsa.rejNTTApi.doc (notes := ["It squeezes 1008 bytes of SHAKE128 output (6 blocks) and \
      runs the loop of `RejNTTPoly` over them."])
    code := Impl.MlDsa.X86_64.Sample.rejNTT
    contract := Spec.MlDsa.rejNTTContract X86_64.abi 16
    stack := 16
    verified := Proof.MlDsa.X86_64.Sample.rejNTT_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.MlDsaSample.X86_64
