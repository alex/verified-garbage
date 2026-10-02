import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Blake2.AArch64.Compress
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Verified

/-! # BLAKE2s (RFC 7693) on AArch64 -/

namespace VG.Artifacts.Blake2s.AArch64

def artifacts : List Artifact := [
  { Spec.Blake2.compressSApi with
    target := AArch64.target
    doc := Spec.Blake2.compressSApi.doc
    code := Impl.Blake2.AArch64.compress Spec.Blake2.s
    contract := Spec.Blake2.compressSContract AArch64.abi
    verified := Proof.Blake2.AArch64.compressS_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blake2.initSApi with
    target := AArch64.target
    doc := Spec.Blake2.initSApi.doc
    code := Impl.Blake2.AArch64.Stream.init Spec.Blake2.s
    contract := Spec.Blake2.initSContract AArch64.abi
    verified := Proof.Blake2.AArch64.Stream.initS_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blake2.updateSApi with
    target := AArch64.target
    doc := Spec.Blake2.updateSApi.doc
    code := Impl.Blake2.AArch64.Stream.update Spec.Blake2.s
    contract := Spec.Blake2.updateSContract AArch64.abi 16
    stack := 16
    verified := Proof.Blake2.AArch64.Stream.updateS_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Blake2.finalizeSApi with
    target := AArch64.target
    doc := Spec.Blake2.finalizeSApi.doc
    code := Impl.Blake2.AArch64.Stream.finalize Spec.Blake2.s
    contract := Spec.Blake2.finalizeSContract AArch64.abi 16
    stack := 16
    verified := Proof.Blake2.AArch64.Stream.finalizeS_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Blake2s.AArch64
