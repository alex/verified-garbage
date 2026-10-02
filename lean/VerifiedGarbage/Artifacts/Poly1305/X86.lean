import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.Poly1305.X86
import VerifiedGarbage.Proof.Poly1305.X86.Init
import VerifiedGarbage.Proof.Poly1305.X86.Update
import VerifiedGarbage.Proof.Poly1305.X86.Finalize
import VerifiedGarbage.Proof.Poly1305.X86.Lit

/-! # Poly1305 (RFC 8439 §2.5) on x86 -/

namespace VG.Artifacts.Poly1305.X86

def artifacts : List Artifact := [
  { Spec.Poly1305.initApi with
    target := X86.target
    doc := Spec.Poly1305.initApi.doc
    code := Impl.Poly1305.X86.init
    contract := Spec.Poly1305.initContract X86.abi
    verified := Proof.Poly1305.X86.init_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Poly1305.blocksApi with
    target := X86.target
    doc := Spec.Poly1305.blocksApi.doc
    code := Impl.Poly1305.X86.blocks
    contract := Spec.Poly1305.blocksContract X86.abi
    verified := Proof.Poly1305.X86.blocks_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Poly1305.updateApi with
    target := X86.target
    doc := Spec.Poly1305.updateApi.doc
    code := Impl.Poly1305.X86.update
    contract := Spec.Poly1305.updateContract X86.abi
    verified := Proof.Poly1305.X86.update_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Poly1305.finalizeApi with
    target := X86.target
    doc := Spec.Poly1305.finalizeApi.doc
    code := Impl.Poly1305.X86.finalize
    contract := Spec.Poly1305.finalizeContract X86.abi
    verified := Proof.Poly1305.X86.finalize_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Poly1305.X86
