import VerifiedGarbage.Proof.Argon2.X86_64.Compress

/-!
# Argon2 compression on x86-64

Registration for the scalar compression primitive. The API and contract
come from the reviewed specification; the code and proof are untrusted.
-/

namespace VG.Artifacts.Argon2.X86_64

def artifacts : List Artifact := [
  { Spec.Argon2.compressApi with
    target := X86_64.target
    doc := Spec.Argon2.compressApi.doc
    code := Impl.Argon2.X86_64.compress
    contract := Spec.Argon2.compressContract X86_64.abi
    stack := 0
    verified := Proof.Argon2.X86_64.compress_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Argon2.X86_64
