import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Verified

/-! # Argon2 H′ for every x86-64 BLAKE2b backend -/

namespace VG.Generic.Blake2b.X86_64.Argon2

def artifacts (v : Proof.Blake2.X86_64.Backend) : List Artifact := [
  { Spec.Argon2.hPrimeApi with
    name := Spec.Argon2.hPrimeApi.name ++ v.suffix
    target := VG.X86_64.target
    doc := Spec.Argon2.hPrimeApi.doc
      (notes := ["Calls the selected BLAKE2b streaming backend for every hash; \
        only argument handling, chaining, and output copying are specific to H′."])
    code := Impl.Argon2.X86_64.HPrime.code (Proof.Argon2.X86_64.HPrime.hash v)
    contract := Spec.Argon2.hPrimeContract VG.X86_64.abi 16
    stack := 16
    verified := Proof.Argon2.X86_64.HPrime.verified v
    spSafe := Proof.Argon2.X86_64.HPrime.spSafe v
    features := v.features }]

end VG.Generic.Blake2b.X86_64.Argon2
