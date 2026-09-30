import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.IO
import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.ConstantTime
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/-! # CBC's function-level contract -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64

def contract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 128⟩
    let iv : Region := ⟨s.gpr .rsi, 8⟩
    let data : Region := ⟨s.gpr .rdx, 8 * (s.gpr .rcx).toNat⟩
    let buf : Region := ⟨s.gpr .r8, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [key] ∧ s.wr = [iv, data, buf] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
      stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
      (s.gpr .rdx).toNat + 8 * (s.gpr .rcx).toNat ≤ 2 ^ 64
  post s s' :=
    let out := Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)) d
      (Spec.Rc2.blockAt s.mem (s.gpr .rsi)) (Spec.Rc2.blocksAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    Spec.Rc2.blocksAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat = out.1 ∧
      Spec.Rc2.blockAt s'.mem (s.gpr .rsi) = out.2
  pub := PublicRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]

end VG.Proof.Rc2.X86_64.Cbc
