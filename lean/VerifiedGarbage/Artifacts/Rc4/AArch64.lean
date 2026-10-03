import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedInit
import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedApply

/-! # Raw RC4 on baseline AArch64 -/
namespace VG.Artifacts.Rc4.AArch64

def artifacts : List Artifact := [
  { Spec.Rc4.initApi with
    target := AArch64.target
    doc := Spec.Rc4.initApi.doc (notes := [
      "The permutation stays in `v16`–`v31` for the whole key schedule: a \
       secret-indexed read is four `tbl`/`tbx` lookups of four registers each, and a \
       write sixteen `cmeq`/`bit` pairs, so no address or branch depends on the key, \
       the table or `j`."])
    code := Impl.Rc4.AArch64.init
    contract := Spec.Rc4.initContract AArch64.abi
    verified := Proof.Rc4.AArch64.init_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.Rc4.applyApi with
    target := AArch64.target
    doc := Spec.Rc4.applyApi.doc (notes := [
      "The permutation stays in `v16`–`v31` for the whole call, rotated so that \
       the public `S[i]` is at a lane fixed in the code: a secret-indexed read is four \
       `tbl`/`tbx` lookups of four registers each, and a write sixteen `cmeq`/`bit` \
       pairs, so no address or branch depends on the table, `j` or the data."])
    code := Impl.Rc4.AArch64.apply
    contract := Spec.Rc4.applyContract AArch64.abi
    verified := Proof.Rc4.AArch64.apply_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Rc4.AArch64
