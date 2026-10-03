import VerifiedGarbage.Proof.TripleDes.AArch64.ConstantTime
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.TripleDes.Contract

namespace VG.Proof.TripleDes.AArch64.Ecb

open VG VG.AArch64

def contract (d : Spec.TripleDes.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 384⟩
    let data : Region := ⟨s.gpr .x1, 8 * (s.gpr .x2).toNat⟩
    let buf : Region := ⟨s.gpr .x3, 1024⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧
      (s.gpr .x1).toNat + 8 * (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) d
        (Spec.TripleDes.blocksAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub := PublicRegs [.x0, .x1, .x2, .x3]

end VG.Proof.TripleDes.AArch64.Ecb
