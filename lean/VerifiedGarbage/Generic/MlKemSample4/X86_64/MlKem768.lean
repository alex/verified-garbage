import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.KgTop
import VerifiedGarbage.Proof.MlKem.X86_64.EcTop
import VerifiedGarbage.Proof.MlKem.X86_64.DcTop

/-!
# ML-KEM-768 (FIPS 203) on x86-64: key generation, encapsulation and decapsulation

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which sample
the matrix `Â` four entries at a time with an implementation `v` of
`vg_mlkem_sample_ntt4`, are emitted once for each implementation
(`Variants/MlKemSample4/X86_64/`), named with its suffix (e.g.
`vg_mlkem768_keygen_avx2`), and need its CPU features. **Review note**:
`sig` and `doc` are trusted, as they tie the Rust caller to the contract;
check them against the contract's `pre`/`post`. An artifact made from a
function's `Api` (in `Spec/`, reviewed with the contract) takes them from
there, and this file adds only notes on the implementation. The emitter adds
the `# Safety` items that depend on the target (`Sig.layoutDoc`), from
`stack` and `writeArgs`, which `ofSig` checks against the contract.
-/

namespace VG.Generic.MlKemSample4.X86_64.MlKem768

open VG.Proof.MlKem.X86_64 (Sample4Impl)

/-- What an instance calls, and its use of the stack. -/
def notes (v : Sample4Impl) : List String :=
  ["The function saves its caller's callee-saved registers in `scratch`; its calls use the 32 bytes of \
    stack below its return address. It samples the matrix four entries at a time with `" ++
    v.callee.name ++ "`."]

def artifacts (v : Sample4Impl) : List Artifact := [
  { Spec.MlKem.keyGenApi with
    name := Spec.MlKem.keyGenApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.MlKem.keyGenApi.doc (notes := notes v)
    code := Impl.MlKem.X86_64.keyGen v.callee
    contract := Spec.MlKem.keyGenContract X86_64.abi 32
    stack := 32
    verified := Proof.MlKem.X86_64.keyGen_verified v
    spSafe := by s4_sp v
    features := v.features },
  { Spec.MlKem.encapsApi with
    name := Spec.MlKem.encapsApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.MlKem.encapsApi.doc (notes := notes v)
    code := Impl.MlKem.X86_64.encaps v.callee
    contract := Spec.MlKem.encapsContract X86_64.abi 32
    stack := 32
    verified := Proof.MlKem.X86_64.encaps_verified v
    spSafe := by s4_sp v
    features := v.features },
  { Spec.MlKem.decapsApi with
    name := Spec.MlKem.decapsApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.MlKem.decapsApi.doc (notes := notes v)
    code := Impl.MlKem.X86_64.decaps v.callee
    contract := Spec.MlKem.decapsContract X86_64.abi 32
    stack := 32
    verified := Proof.MlKem.X86_64.decaps_verified v
    spSafe := by s4_sp v
    features := v.features }]

end VG.Generic.MlKemSample4.X86_64.MlKem768
