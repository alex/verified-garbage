import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Blake2.AArch64.Compress
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Verified

/-! # BLAKE2b (RFC 7693) on AArch64 -/

namespace VG.Artifacts.Blake2b.AArch64

def artifacts : List Artifact := [
  { Spec.Blake2.compressBApi with
    target := AArch64.target
    doc := Spec.Blake2.compressBApi.doc
    code := Impl.Blake2.AArch64.compress Spec.Blake2.b
    contract := Spec.Blake2.compressBContract AArch64.abi
    verified := Proof.Blake2.AArch64.compressB_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blake2.initBApi with
    target := AArch64.target
    doc := Spec.Blake2.initBApi.doc
    code := Impl.Blake2.AArch64.Stream.init Spec.Blake2.b
    contract := Spec.Blake2.initBContract AArch64.abi
    verified := Proof.Blake2.AArch64.Stream.initB_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blake2.updateBApi with
    target := AArch64.target
    doc := Spec.Blake2.updateBApi.doc
    code := Impl.Blake2.AArch64.Stream.update Spec.Blake2.b
    contract := Spec.Blake2.updateBContract AArch64.abi 16
    stack := 16
    verified := Proof.Blake2.AArch64.Stream.updateB_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blake2.finalizeBApi with
    target := AArch64.target
    doc := Spec.Blake2.finalizeBApi.doc
    code := Impl.Blake2.AArch64.Stream.finalize Spec.Blake2.b
    contract := Spec.Blake2.finalizeBContract AArch64.abi 16
    stack := 16
    verified := Proof.Blake2.AArch64.Stream.finalizeB_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Blake2b.AArch64
