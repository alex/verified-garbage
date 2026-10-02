import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Verified

/-! Streaming absorb is emitted for every verified whole-block CMAC update
variant. Its buffering proof depends on the update contract, not on CTR. -/
namespace VG.Generic.CmacAesUpdate.AArch64.Absorb
def artifacts (v : Proof.CmacAes.AArch64.UpdateImpl) : List Artifact := [
  { Spec.Cmac.aesAbsorbApi with
    name := Spec.Cmac.aesAbsorbApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.Cmac.aesAbsorbApi.doc (notes := ["This implementation chains blocks with `" ++ v.callee.name ++ "`."])
    code := Impl.CmacAes.Stream.AArch64.absorb v.callee
    contract := Spec.Cmac.aesAbsorbContract AArch64.abi
    verified := Proof.CmacAes.Stream.AArch64.absorb_verified v
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]
end VG.Generic.CmacAesUpdate.AArch64.Absorb
