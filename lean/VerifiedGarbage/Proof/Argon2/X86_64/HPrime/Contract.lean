import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-! # H′: a local x86-64 contract -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64

def inputR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def outputR (s : State) : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
def workR (s : State) : Region := ⟨s.gpr .r8, 16384⟩
def retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩
def stackR (s : State) : Region := below (s.gpr .rsp) 16

def localContract : Contract isa where
  pre s := s.rd = [inputR s] ∧ s.wr = [outputR s, workR s] ∧
    (s.gpr .rsi).toNat < 2 ^ 32 ∧ 1 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat < 2 ^ 32 ∧
    (inputR s).Disjoint (workR s) ∧ (outputR s).Disjoint (workR s) ∧
    (stackR s).Disjoint (inputR s) ∧ (stackR s).Disjoint (outputR s) ∧ (stackR s).Disjoint (workR s) ∧
    (retR s).Disjoint (outputR s) ∧ (retR s).Disjoint (workR s)
  post s t := Spec.Blake2.bytesAt t.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    Spec.Argon2.hPrime (s.gpr .rcx).toNat (Spec.Blake2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s t := s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .rsp = t.gpr .rsp

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 1⟩, ⟨0x4000, 16384⟩]

theorem contract_implies : localContract.Implies (Spec.Argon2.hPrimeContract X86_64.abi 16) := by
  sig_implies [Spec.Argon2.hPrimeContract, Spec.Argon2.hPrimeSig, localContract,
    inputR, outputR, workR, retR, stackR, below, X86_64.abi, X86_64.argRegs] [satState] using satState

end VG.Proof.Argon2.X86_64.HPrime
