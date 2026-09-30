import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.IO
import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.ConstantTime
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/-! # CBC's function-level contract -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

def contract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 128⟩
    let iv : Region := ⟨s.gpr .x1, 8⟩
    let data : Region := ⟨s.gpr .x2, 8 * (s.gpr .x3).toNat⟩
    let buf : Region := ⟨s.gpr .x4, 512⟩
    s.rd = [key] ∧ s.wr = [iv, data, buf] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      (s.gpr .x2).toNat + 8 * (s.gpr .x3).toNat ≤ 2 ^ 64
  post s s' :=
    let out := Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .x1)) (Spec.Rc2.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    Spec.Rc2.blocksAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat = out.1 ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .x1) = out.2
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4]

end VG.Proof.Rc2.AArch64.Cbc
