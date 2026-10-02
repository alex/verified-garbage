import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.ChaCha20.AArch64.Block
import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit

/-! # The ChaCha20 block function (RFC 8439) on AArch64 -/

namespace VG.Artifacts.ChaCha20.AArch64

def artifacts : List Artifact := [
  { Spec.ChaCha20.blockApi with
    target := AArch64.target
    doc := Spec.ChaCha20.blockApi.doc
    code := Impl.ChaCha20.AArch64.block
    contract := Spec.ChaCha20.blockContract AArch64.abi
    verified := Proof.ChaCha20.AArch64.block_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.ChaCha20.AArch64
