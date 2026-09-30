import VerifiedGarbage.Proof.Rc2.Arm.Cbc.IO
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/-! # CBC's function-level contract -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

def contract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let iv : Region := ⟨State.addr (s.gpr .r1), 8⟩
    let data : Region := ⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩
    let buf : Region := ⟨State.addr (stackArg s 0), 512⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [key, args] ∧ s.wr = [iv, data, buf] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧ iv.Disjoint args ∧ data.Disjoint args ∧ buf.Disjoint args ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 8 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 512 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32
  post s s' :=
    let out := Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r1))) (Spec.Rc2.blocksAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    Spec.Rc2.blocksAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat = out.1 ∧
      Spec.Rc2.blockAt s'.mem (State.addr (s.gpr .r1)) = out.2
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Rc2.Arm.Cbc
