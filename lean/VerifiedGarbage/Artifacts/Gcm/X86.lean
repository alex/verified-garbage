import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Gcm.X86.Ghash

/-! # GHASH on x86 -/

namespace VG.Artifacts.Gcm.X86

def artifacts : List Artifact := [
  { Spec.Gcm.ghashApi with
    target := X86.target
    doc := Spec.Gcm.ghashApi.doc
      (notes := ["`•` is computed bit by bit as Algorithm 1 of §6.3 does, with masks instead of \
        branches."])
    code := Impl.Gcm.X86.ghash
    contract := Spec.Gcm.ghashContract X86.abi
    verified := Proof.Gcm.X86.ghash_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Gcm.X86
