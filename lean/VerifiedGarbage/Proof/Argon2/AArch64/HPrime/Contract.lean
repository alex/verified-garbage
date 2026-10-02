import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-! # H′: a local ARM64 contract -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64

def inputR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
def outputR (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
def workR (s : State) : Region := ⟨s.gpr .x4, 16384⟩
def stackR (s : State) : Region := below s.sp 16

def localContract : Contract isa where
  pre s := s.rd = [inputR s] ∧ s.wr = [outputR s, workR s] ∧
    (s.gpr .x1).toNat < 2 ^ 32 ∧ 1 ≤ (s.gpr .x3).toNat ∧ (s.gpr .x3).toNat < 2 ^ 32 ∧
    16 ≤ s.sp.toNat ∧
    (inputR s).Disjoint (workR s) ∧ (outputR s).Disjoint (workR s) ∧
    (stackR s).Disjoint (inputR s) ∧ (stackR s).Disjoint (outputR s) ∧ (stackR s).Disjoint (workR s)
  post s t := Spec.Blake2.bytesAt t.mem (s.gpr .x2) (s.gpr .x3).toNat =
    Spec.Argon2.hPrime (s.gpr .x3).toNat (Spec.Blake2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s t := s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4 ∧ s.sp = t.sp

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 0x2000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x9000
  c := false
  v _ := 0
  unknowns _ := 0
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 1⟩, ⟨0x4000, 16384⟩]

theorem contract_implies : localContract.Implies (Spec.Argon2.hPrimeContract AArch64.abi 16) := by
  sig_implies [Spec.Argon2.hPrimeContract, Spec.Argon2.hPrimeSig, localContract,
    inputR, outputR, workR, stackR, below, AArch64.abi, AArch64.argRegs] [satState] using satState

end VG.Proof.Argon2.AArch64.HPrime
