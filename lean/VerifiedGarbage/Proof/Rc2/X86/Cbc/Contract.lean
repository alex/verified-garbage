import VerifiedGarbage.Proof.Rc2.X86.Cbc.IO
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

namespace VG.Proof.Rc2.X86.Cbc
open VG VG.X86

def contract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), 128⟩
    let iv : Region := ⟨addr32 (arg s 1), 8⟩
    let data : Region := ⟨addr32 (arg s 2), 8 * (arg s 3).toNat⟩
    let buf : Region := ⟨addr32 (arg s 4), 512⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    let stack := below (s.gpr .esp) 16
    s.rd = [key, args] ∧ s.wr = [iv, data, buf] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      args.Disjoint iv ∧ args.Disjoint data ∧ args.Disjoint buf ∧
      ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
      stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
      16 ≤ (s.gpr .esp).toNat ∧ (arg s 2).toNat + 8 * (arg s 3).toNat ≤ 2 ^ 32
  post s s' :=
    let out := Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))) d
      (Spec.Rc2.blockAt s.mem (addr32 (arg s 1))) (Spec.Rc2.blocksAt s.mem (addr32 (arg s 2)) (arg s 3).toNat)
    Spec.Rc2.blocksAt s'.mem (addr32 (arg s 2)) (arg s 3).toNat = out.1 ∧
      Spec.Rc2.blockAt s'.mem (addr32 (arg s 1)) = out.2
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Rc2.X86.Cbc
