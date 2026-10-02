import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Poly1305.AArch64.Radix64
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Blocks
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Finalize
import VerifiedGarbage.Proof.Poly1305.AArch64.Init
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Update
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit

/-! # Poly1305 (RFC 8439 §2.5) on AArch64 -/

namespace VG.Artifacts.Poly1305.AArch64

def artifacts : List Artifact := [
  { Spec.Poly1305.initApi with
    target := AArch64.target
    doc := Spec.Poly1305.initApi.doc
    code := Impl.Poly1305.AArch64.init
    contract := Spec.Poly1305.initContract AArch64.abi
    verified := Proof.Poly1305.AArch64.init_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Poly1305.blocksApi with
    target := AArch64.target
    doc := Spec.Poly1305.blocksApi.doc
    code := Impl.Poly1305.AArch64.Radix64.blocks
    contract := Spec.Poly1305.blocksContract AArch64.abi
    verified := Proof.Poly1305.AArch64.Radix64.blocks_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Poly1305.updateApi with
    target := AArch64.target
    doc := Spec.Poly1305.updateApi.doc
    code := Impl.Poly1305.AArch64.Radix64.update
    contract := Spec.Poly1305.updateContract AArch64.abi
    verified := Proof.Poly1305.AArch64.Radix64.update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Poly1305.finalizeApi with
    target := AArch64.target
    doc := Spec.Poly1305.finalizeApi.doc
    code := Impl.Poly1305.AArch64.Radix64.finalize
    contract := Spec.Poly1305.finalizeContract AArch64.abi
    verified := Proof.Poly1305.AArch64.Radix64.finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Poly1305.AArch64
