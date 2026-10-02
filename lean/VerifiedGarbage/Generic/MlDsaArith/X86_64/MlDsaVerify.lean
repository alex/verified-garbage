import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims

/-!
# ML-DSA (FIPS 204) on x86-64: verification

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which call an
implementation `v` of the polynomial arithmetic (`vg_mldsa_ntt`, …), are
emitted once for each implementation (`Variants/MlDsaArith/X86_64/`), named
with its suffix (e.g. `vg_mldsa44_verify_avx2`), and need its CPU features.

The stack is 32 bytes: the return address of a call of a primitive, and up
to 24 bytes for its own calls (`vg_mldsa_rej_ntt_poly4`'s).
-/

namespace VG.Generic.MlDsaArith.X86_64.MlDsaVerify

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Verify (primsWith prims_okWith verify_prims verify_spSafe)

/-- What the documentation says of the implementation. -/
def note : String :=
  "It calls the `vg_mldsa_*` primitives and the SHAKE256 sponge. The samplers' results are combined \
  without a branch, so the only branches depend on the public key and the signature."

def artifacts (v : ArithImpl) : List Artifact := [
  { Spec.MlDsa.verify44Api with
    name := Spec.MlDsa.verify44Api.name ++ v.code.sfx
    features := v.features
    target := X86_64.target
    doc := Spec.MlDsa.verify44Api.doc (notes := [note])
    code := Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa44
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 X86_64.abi 32
    stack := 32
    verified := verify_prims v (List.mem_cons_self ..)
    spSafe := verify_spSafe (prims_okWith v) (List.mem_cons_self ..) },
  { Spec.MlDsa.verify65Api with
    name := Spec.MlDsa.verify65Api.name ++ v.code.sfx
    features := v.features
    target := X86_64.target
    doc := Spec.MlDsa.verify65Api.doc (notes := [note])
    code := Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa65
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 X86_64.abi 32
    stack := 32
    verified := verify_prims v (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  { Spec.MlDsa.verify87Api with
    name := Spec.MlDsa.verify87Api.name ++ v.code.sfx
    features := v.features
    target := X86_64.target
    doc := Spec.MlDsa.verify87Api.doc (notes := [note])
    code := Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa87
    contract := Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 X86_64.abi 32
    stack := 32
    verified := verify_prims v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) }]

end VG.Generic.MlDsaArith.X86_64.MlDsaVerify
