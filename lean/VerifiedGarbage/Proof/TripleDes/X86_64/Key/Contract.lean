import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Body
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Save
import VerifiedGarbage.Proof.TripleDes.X86_64.ConstantTime
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Spec.TripleDes.Contract

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let output : Region := ⟨s.gpr .rdx, 384⟩
    let scratch : Region := ⟨s.gpr .rcx, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [output, scratch] ∧ key.Disjoint output ∧ key.Disjoint scratch ∧
      output.Disjoint scratch ∧ ret.Disjoint output ∧ ret.Disjoint scratch ∧
      Spec.TripleDes.validKey (s.gpr .rsi).toNat
  post s s' := Spec.TripleDes.scheduleAt s'.mem (s.gpr .rdx) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub := PublicRegs [.rdi, .rsi, .rdx, .rcx]

end VG.Proof.TripleDes.X86_64.Key
