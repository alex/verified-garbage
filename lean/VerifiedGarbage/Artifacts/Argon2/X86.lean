import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Argon2.X86.CompressVerified
import VerifiedGarbage.Proof.Argon2.X86.HPrime.Verified
import VerifiedGarbage.Proof.Argon2.X86.Derive.Verified

/-! # Argon2 (RFC 9106) on x86 -/

namespace VG.Artifacts.Argon2.X86

def artifacts : List Artifact := [
  { Spec.Argon2.compressApi with
    target := X86.target
    doc := Spec.Argon2.compressApi.doc
    code := Impl.Argon2.X86.compress
    contract := Spec.Argon2.compressContract X86.abi
    stack := 0
    verified := Proof.Argon2.X86.compressShared_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Argon2.hPrimeApi with
    target := X86.target
    doc := Spec.Argon2.hPrimeApi.doc
    code := Impl.Argon2.X86.HPrime.code
    contract := Spec.Argon2.hPrimeContract X86.abi 60
    stack := 60
    verified := Proof.Argon2.X86.HPrime.hPrimeShared_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Argon2.deriveApi with
    target := X86.target
    doc := Spec.Argon2.deriveApi.doc
    code := Impl.Argon2.X86.Derive.derive
    contract := Spec.Argon2.deriveContract X86.abi 244
    stack := 244
    verified := Proof.Argon2.X86.Derive.deriveShared_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Argon2.X86
