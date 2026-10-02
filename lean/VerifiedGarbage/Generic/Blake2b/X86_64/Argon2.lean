import VerifiedGarbage.Proof.Argon2.X86_64.DeriveVerified

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
    features := v.features },
  { Spec.Argon2.deriveApi with
    name := Spec.Argon2.deriveApi.name ++ v.suffix
    target := VG.X86_64.target
    doc := Spec.Argon2.deriveApi.doc
      (notes := ["Serial lane evaluation honors every positive worker limit. All hashing uses \
        the selected BLAKE2b streaming backend, including H₀ and every H′ call."])
    code := Impl.Argon2.X86_64.Derive.code (Spec.Argon2.hPrimeApi.name ++ v.suffix)
      (Proof.Argon2.X86_64.HPrime.hash v)
    contract := Spec.Argon2.deriveContract VG.X86_64.abi 344
    stack := 344
    verified := Proof.Argon2.X86_64.Derive.verified v _
    spSafe := Proof.Argon2.X86_64.Derive.code_spSafe v _
    features := v.features }]

end VG.Generic.Blake2b.X86_64.Argon2
