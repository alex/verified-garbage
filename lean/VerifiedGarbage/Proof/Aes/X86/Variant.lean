import VerifiedGarbage.Impl.Aes.X86.Callee
import VerifiedGarbage.Proof.Aes.X86.Ctr32CT
import VerifiedGarbage.Proof.Aes.X86.ExpandKeyCT
import VerifiedGarbage.Proof.Framework.X86.Call

/-! Contracts and execution properties that every x86 AES variant supplies to callers. -/
namespace VG.Proof.Aes.X86
open VG.X86
structure Ctr32Impl where
  callee : Impl.Aes.X86.Ctr32
  depth : stackUse callee.code = 0
  stack : stackUse callee.code = 0
  ok : ∀ s, Proof.Aes.ctr32X86.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32X86.post s s'
  ct : ConstantTime isa Proof.Aes.ctr32X86.pre Proof.Aes.ctr32X86.pub callee.code
  nosp : NoSp callee.code
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  suffix : String
  features : List String
  expand : Impl.Aes.X86.ExpandKey
  expandDepth : stackUse expand.code = 0
  expandStack : stackUse expand.code = 0
  expandOk : ∀ s, Proof.Aes.expandKeyX86.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyX86.post s s'
  expandCt : ConstantTime isa Proof.Aes.expandKeyX86.pre Proof.Aes.expandKeyX86.pub expand.code
  expandNosp : NoSp expand.code
  expandSpSafe : expand.code.all (fun i => !isa.writesSp i) = true
end VG.Proof.Aes.X86
