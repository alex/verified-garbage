import VerifiedGarbage.Proof.TripleDes.Arm.Ecb.IO
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.TripleDes.Contract

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm

def contract (d : Spec.TripleDes.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 384⟩
    let data : Region := ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩
    let buf : Region := ⟨State.addr (s.gpr .r3), 1024⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧
      (s.gpr .r1).toNat + 8 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧ (s.gpr .r0).toNat + 384 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 1024 ≤ 2 ^ 32
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d
        (Spec.TripleDes.blocksAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
  pub := PublicRegs [.r0, .r1, .r2, .r3]

end VG.Proof.TripleDes.Arm.Ecb
