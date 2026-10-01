import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Inst

/-!
# ML-DSA (FIPS 204) on x86-64: key generation

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which call an
implementation `v` of the polynomial arithmetic (`vg_mldsa_ntt`, …), are
emitted once for each implementation (`Variants/MlDsaArith/X86_64/`), named
with its suffix (e.g. `vg_mldsa44_keygen_avx2`), and need its CPU features.
**Review note**: `sig` and `doc` are trusted, as they tie the Rust caller to
the contract; check them against the contract's `pre`/`post`. Each artifact
is made from its function's `Api` (in `Spec/MlDsa/Contract.lean`, reviewed
with the contract), and this file adds only notes on the implementation. The
emitter adds the `# Safety` items that depend on the target
(`Sig.layoutDoc`), from `stack` and `writeArgs`, which `ofSig` checks
against the contract.
-/

namespace VG.Generic.MlDsaArith.X86_64.MlDsaKeyGen

open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Impl.MlDsa.X86_64.KeyGen (keyGen primsWith)

/-- Notes on the implementation, the same for every parameter set. -/
def notes : List String :=
  ["The function saves its caller's callee-saved registers in `scratch`; its calls use the 32 \
    bytes of stack below its return address.",
   "It samples every polynomial of `A` and of `s1` and `s2` whatever the samplers return, and \
    zeroes the polynomial of a sampler that fails rather than branching on it: its timing does not \
    depend on whether key generation fails."]

def artifacts (v : ArithImpl) : List Artifact := [
  { Spec.MlDsa.keyGen44Api with
    name := Spec.MlDsa.keyGen44Api.name ++ v.code.sfx
    features := v.features
    target := X86_64.target
    doc := Spec.MlDsa.keyGen44Api.doc (notes := notes)
    code := keyGen (primsWith v.code) Spec.MlDsa.mlDsa44
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 X86_64.abi 32
    stack := 32
    verified := Proof.MlDsa.X86_64.KeyGen.keyGen_verifiedWith v (.inl rfl)
    spSafe := Proof.MlDsa.X86_64.KeyGen.keyGen_spSafe v (.inl rfl) },
  { Spec.MlDsa.keyGen65Api with
    name := Spec.MlDsa.keyGen65Api.name ++ v.code.sfx
    features := v.features
    target := X86_64.target
    doc := Spec.MlDsa.keyGen65Api.doc (notes := notes)
    code := keyGen (primsWith v.code) Spec.MlDsa.mlDsa65
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 X86_64.abi 32
    stack := 32
    verified := Proof.MlDsa.X86_64.KeyGen.keyGen_verifiedWith v (.inr (.inl rfl))
    spSafe := Proof.MlDsa.X86_64.KeyGen.keyGen_spSafe v (.inr (.inl rfl)) },
  { Spec.MlDsa.keyGen87Api with
    name := Spec.MlDsa.keyGen87Api.name ++ v.code.sfx
    features := v.features
    target := X86_64.target
    doc := Spec.MlDsa.keyGen87Api.doc (notes := notes)
    code := keyGen (primsWith v.code) Spec.MlDsa.mlDsa87
    contract := Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 X86_64.abi 32
    stack := 32
    verified := Proof.MlDsa.X86_64.KeyGen.keyGen_verifiedWith v (.inr (.inr rfl))
    spSafe := Proof.MlDsa.X86_64.KeyGen.keyGen_spSafe v (.inr (.inr rfl)) }]

end VG.Generic.MlDsaArith.X86_64.MlDsaKeyGen
