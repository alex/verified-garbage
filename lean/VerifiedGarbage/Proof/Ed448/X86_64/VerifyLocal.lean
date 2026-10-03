import VerifiedGarbage.Impl.Ed448.X86_64.VerifyEquation
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 verification's equation on x86-64: the contract the proof is written against

The facts of `Spec.Ed448.verifyEquationContract` the proof uses, stated for
x86-64, in a module of their own: callers proven for any code meeting them
need not import the proof, and the group theory it imports.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64

/-- `vg_ed448_verify_equation(pk = rdi, signature = rsi, challenge = rdx, scratch = rcx) -> eax`. -/
def verifyEquationLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .rdi, 57⟩, ⟨s.gpr .rsi, 114⟩, ⟨s.gpr .rdx, 57⟩] ∧
    s.wr = [⟨s.gpr .rcx, 8192⟩] ∧
    (⟨s.gpr .rdi, 57⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rsi, 114⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rdx, 57⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64
  post s t := t.gpr .rax = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .rdi) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .rsi) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .rdx) 57) then 1 else 0
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx

end VG.Proof.Ed448.X86_64
