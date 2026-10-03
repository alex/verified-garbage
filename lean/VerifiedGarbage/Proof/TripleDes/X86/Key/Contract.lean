import VerifiedGarbage.Proof.TripleDes.X86.Key.Entry

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), (arg s 1).toNat⟩
    let output : Region := ⟨addr32 (arg s 2), 384⟩
    let scratch : Region := ⟨addr32 (arg s 3), 512⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    s.rd = [key, args] ∧ s.wr = [output, scratch] ∧ key.Disjoint output ∧
      key.Disjoint scratch ∧ output.Disjoint scratch ∧ args.Disjoint output ∧
      args.Disjoint scratch ∧ ret.Disjoint output ∧ ret.Disjoint scratch ∧
      Spec.TripleDes.validKey (arg s 1).toNat ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 512 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' := Spec.TripleDes.scheduleAt s'.mem (addr32 (arg s 2)) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (addr32 (arg s 0)) (arg s 1).toNat)
  pub s t := s.gpr .esp = t.gpr .esp ∧ ∀ i < 4, arg s i = arg t i

end VG.Proof.TripleDes.X86.Key
