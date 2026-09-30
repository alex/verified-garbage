import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.EcTop
import VerifiedGarbage.Proof.MlKem.X86_64.KgXVerified
import VerifiedGarbage.Proof.MlKem.X86_64.XeXVerified

/-!
# ML-KEM-768 (FIPS 203) on x86-64: key generation, encapsulation and key expansion

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which sample
the matrix `Â` four entries at a time with an implementation `v` of
`vg_mlkem_sample_ntt4`, are emitted once for each implementation
(`Variants/MlKemSample4/X86_64/`), named with its suffix (e.g.
`vg_mlkem768_keygen_expanded_avx2`), and need its CPU features. The
functions that take an expanded key sample nothing
(`Artifacts/MlKemExpanded/X86_64.lean`). The Rust code generates keys with
`vg_mlkem768_keygen_expanded` and decapsulates with the expanded key, so
`vg_mlkem768_keygen` and `vg_mlkem768_decaps` are not emitted on x86-64
(their proofs remain, and those of the expanded functions build on them).
It encapsulates to a key it did not expand with `vg_mlkem768_encaps`.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller
to the contract; check them against the contract's `pre`/`post`. An
artifact made from a function's `Api` (in `Spec/`, reviewed with the
contract) takes them from there, and this file adds only notes on the
implementation. The emitter adds the `# Safety` items that depend on the
target (`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig`
checks against the contract.
-/

namespace VG.Generic.MlKemSample4.X86_64.MlKem768

open VG.Proof.MlKem.X86_64 (Sample4Impl)

/-- What an instance calls, and its use of the stack. -/
def notes (v : Sample4Impl) : List String :=
  ["The function saves its caller's callee-saved registers in `scratch`; its calls use the 32 bytes of \
    stack below its return address. It samples the matrix four entries at a time with `" ++
    v.callee.name ++ "`."]

def artifacts (v : Sample4Impl) : List Artifact := [
  { Spec.MlKem.keyGenExpandedApi with
    name := Spec.MlKem.keyGenExpandedApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.MlKem.keyGenExpandedApi.doc (notes := notes v)
    code := Impl.MlKem.X86_64.keyGenX v.callee
    contract := Spec.MlKem.keyGenExpandedContract X86_64.abi 32
    stack := 32
    verified := Proof.MlKem.X86_64.keyGenX_verified v
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
  { Spec.MlKem.expandEkApi with
    name := Spec.MlKem.expandEkApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.MlKem.expandEkApi.doc (notes := notes v)
    code := Impl.MlKem.X86_64.expandEk v.callee
    contract := Spec.MlKem.expandEkContract X86_64.abi 32
    stack := 32
    verified := Proof.MlKem.X86_64.expandEk_verified v
    spSafe := by s4_sp v
    features := v.features }]

end VG.Generic.MlKemSample4.X86_64.MlKem768
