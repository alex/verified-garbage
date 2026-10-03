import VerifiedGarbage.Proof.Argon2.AArch64.DeriveVerified

/-! # Argon2 H′ for every ARM64 BLAKE2b backend -/

namespace VG.Generic.Blake2b.AArch64.Argon2

def artifacts (v : Proof.Argon2.AArch64.HPrime.Backend) : List Artifact := [
  { Spec.Argon2.hPrimeApi with
    name := Spec.Argon2.hPrimeApi.name ++ v.suffix
    target := VG.AArch64.target
    doc := Spec.Argon2.hPrimeApi.doc
      (notes := ["Calls the selected BLAKE2b streaming backend for every hash; \
        only argument handling, chaining, and output copying are specific to H′."])
    code := Impl.Argon2.AArch64.HPrime.code v.hash
    contract := Spec.Argon2.hPrimeContract VG.AArch64.abi 16
    stack := 16
    verified := Proof.Argon2.AArch64.HPrime.verified v
    spSafe := Proof.Argon2.AArch64.HPrime.spSafe v
    features := v.features },
  { Spec.Argon2.deriveApi with
    name := Spec.Argon2.deriveApi.name ++ v.suffix
    target := VG.AArch64.target
    doc := Spec.Argon2.deriveApi.doc
      (notes := ["Serial lane evaluation honors every positive worker limit. All hashing uses \
        the selected BLAKE2b streaming backend, including H₀ and every H′ call."])
    code := Impl.Argon2.AArch64.Derive.code (Spec.Argon2.hPrimeApi.name ++ v.suffix)
      v.hash
    contract := Spec.Argon2.deriveContract VG.AArch64.abi 400
    stack := 400
    verified := Proof.Argon2.AArch64.Derive.verified v _
    spSafe := Proof.Argon2.AArch64.Derive.code_spSafe v _
    features := v.features }]

end VG.Generic.Blake2b.AArch64.Argon2
