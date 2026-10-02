import VerifiedGarbage.Proof.TripleDes.X86.Ecb.IO
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.TripleDes.Contract

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

def contract (d : Spec.TripleDes.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), 384⟩
    let data : Region := ⟨addr32 (arg s 1), 8 * (arg s 2).toNat⟩
    let buf : Region := ⟨addr32 (arg s 3), 1024⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    let stack := below (s.gpr .esp) 16
    s.rd = [key, args] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ args.Disjoint data ∧ args.Disjoint buf ∧
      ret.Disjoint data ∧ ret.Disjoint buf ∧ stack.Disjoint key ∧ stack.Disjoint data ∧
      stack.Disjoint buf ∧ (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 1024 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      16 ≤ (s.gpr .esp).toNat ∧ (arg s 1).toNat + 8 * (arg s 2).toNat ≤ 2 ^ 32
  post s s' := Spec.TripleDes.blocksAt s'.mem (addr32 (arg s 1)) (arg s 2).toNat =
    Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0))) d
      (Spec.TripleDes.blocksAt s.mem (addr32 (arg s 1)) (arg s 2).toNat)
  pub s t := s.gpr .esp = t.gpr .esp ∧ ∀ i < 4, arg s i = arg t i

end VG.Proof.TripleDes.X86.Ecb
