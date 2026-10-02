import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.Top768
import VerifiedGarbage.Proof.MlKem1024.X86_64.Top

/-!
# ML-KEM-768 and ML-KEM-1024 (FIPS 203) on x86-64: key generation, encapsulation and decapsulation

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which sample the
matrix `Â` four entries at a time with an implementation `v` of
`vg_mlkem_sample_ntt4` (and compute the outputs of `PRF` as goes with it), are
emitted once for each implementation (`Variants/MlKemSample4/X86_64/`), named
with its suffix (e.g. `vg_mlkem768_keygen_avx2`), and need its CPU features.
Both parameter sets are the same code and proofs for their layouts
(`Impl/MlKem/X86_64/Kem.lean`).
-/

namespace VG.Generic.MlKemSample4.X86_64.MlKem

open VG.Proof.MlKem.X86_64 (Sample4Impl)

/-- What an instance calls, and its use of the stack. -/
def notes (v : Sample4Impl) : List String :=
  ["The function saves its caller's callee-saved registers in `scratch`; its calls use the 32 bytes of \
    stack below its return address. It samples the matrix four entries at a time with `" ++
    v.callee.name ++ "`, and computes the outputs of `PRF` " ++ v.prfsDoc ++ "."]

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
    features := v.features },
  { Spec.MlKem1024.keyGenApi with
    name := Spec.MlKem1024.keyGenApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.MlKem1024.keyGenApi.doc (notes := notes v)
    code := Impl.MlKem1024.X86_64.keyGen1024 v.callee
    contract := Spec.MlKem1024.keyGenContract X86_64.abi 32
    stack := 32
    verified := Proof.MlKem1024.X86_64.keyGen1024_verified v
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
  { Spec.MlKem1024.decapsApi with
    name := Spec.MlKem1024.decapsApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.MlKem1024.decapsApi.doc (notes := notes v)
    code := Impl.MlKem1024.X86_64.decaps1024 v.callee
    contract := Spec.MlKem1024.decapsContract X86_64.abi 32
    stack := 32
    verified := Proof.MlKem1024.X86_64.decaps1024_verified v
    spSafe := by s4_sp v
    features := v.features }]

end VG.Generic.MlKemSample4.X86_64.MlKem
