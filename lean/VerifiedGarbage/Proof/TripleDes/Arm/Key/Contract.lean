import VerifiedGarbage.Proof.TripleDes.Arm.Key.Body
import VerifiedGarbage.Proof.TripleDes.Arm.Key.Save
import VerifiedGarbage.Proof.TripleDes.Arm.ConstantTime
import VerifiedGarbage.Spec.TripleDes.Contract

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨(State.addr (s.gpr .r0)), (s.gpr .r1).toNat⟩
    let output : Region := ⟨(State.addr (s.gpr .r2)), 384⟩
    let scratch : Region := ⟨(State.addr (s.gpr .r3)), 512⟩
    s.rd = [key] ∧ s.wr = [output, scratch] ∧ key.Disjoint output ∧ key.Disjoint scratch ∧
      output.Disjoint scratch ∧
      Spec.TripleDes.validKey (s.gpr .r1).toNat ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 384 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 512 ≤ 2 ^ 32
  post s s' := Spec.TripleDes.scheduleAt s'.mem ((State.addr (s.gpr .r2))) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem ((State.addr (s.gpr .r0))) (s.gpr .r1).toNat)
  pub := PublicRegs [.r0, .r1, .r2, .r3]

end VG.Proof.TripleDes.Arm.Key
