import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem1024.X86_64.EcTop
import VerifiedGarbage.Proof.MlKem1024.X86_64.KgXVerified
import VerifiedGarbage.Proof.MlKem1024.X86_64.XeXVerified

/-!
# ML-KEM-1024 (FIPS 203) on x86-64: key generation, encapsulation and key expansion

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which sample
the matrix `Â` four entries at a time with an implementation `v` of
`vg_mlkem_sample_ntt4`, are emitted once for each implementation
(`Variants/MlKemSample4/X86_64/`), named with its suffix (e.g.
`vg_mlkem1024_keygen_expanded_avx2`), and need its CPU features. The
functions that take an expanded key sample nothing
(`Artifacts/MlKem1024Expanded/X86_64.lean`). The Rust code generates keys
with `vg_mlkem1024_keygen_expanded` and decapsulates with the expanded key,
so `vg_mlkem1024_keygen` and `vg_mlkem1024_decaps` are not emitted on
x86-64 (their proofs remain, and those of the expanded functions build on
them).
It encapsulates to a key it did not expand with `vg_mlkem1024_encaps`.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller
to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig`
checks against the contract.
-/

namespace VG.Generic.MlKemSample4.X86_64.MlKem1024

open VG.Proof.MlKem.X86_64 (Sample4Impl)

/-- What an instance calls, and its use of the stack. -/
def notes (v : Sample4Impl) : List String :=
  ["The function saves its caller's callee-saved registers in `scratch`; its calls use the 32 bytes of \
    stack below its return address. It samples the matrix four entries at a time with `" ++
    v.callee.name ++ "`."]

def artifacts (v : Sample4Impl) : List Artifact := [
  { Spec.MlKem1024.keyGenExpandedApi with
    name := Spec.MlKem1024.keyGenExpandedApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.MlKem1024.keyGenExpandedApi.doc (notes := notes v)
    code := Impl.MlKem1024.X86_64.keyGenX1024 v.callee
    contract := Spec.MlKem1024.keyGenExpandedContract X86_64.abi 32
    stack := 32
    verified := Proof.MlKem1024.X86_64.keyGenX1024_verified v
    spSafe := by s4_sp v
    features := v.features },
  { Spec.MlKem1024.encapsApi with
    name := Spec.MlKem1024.encapsApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.MlKem1024.encapsApi.doc (notes := notes v)
    code := Impl.MlKem1024.X86_64.encaps1024 v.callee
    contract := Spec.MlKem1024.encapsContract X86_64.abi 32
    stack := 32
    verified := Proof.MlKem1024.X86_64.encaps1024_verified v
    spSafe := by s4_sp v
    features := v.features },
  { Spec.MlKem1024.expandEkApi with
    name := Spec.MlKem1024.expandEkApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.MlKem1024.expandEkApi.doc (notes := notes v)
    code := Impl.MlKem1024.X86_64.expandEk1024 v.callee
    contract := Spec.MlKem1024.expandEkContract X86_64.abi 32
    stack := 32
    verified := Proof.MlKem1024.X86_64.expandEk1024_verified v
    spSafe := by s4_sp v
    features := v.features }]

end VG.Generic.MlKemSample4.X86_64.MlKem1024
