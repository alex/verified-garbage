import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-! # A local contract for Argon2 block compression -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Spec.Argon2

def compressLocal : Contract isa where
  pre s :=
    let x : Region := ⟨s.gpr .rdi, 1024⟩
    let y : Region := ⟨s.gpr .rsi, 1024⟩
    let out : Region := ⟨s.gpr .rdx, 1024⟩
    let scratch : Region := ⟨s.gpr .rcx, 4096⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [x, y] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ x.Disjoint scratch ∧ y.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch
  post s t := blockAt t.mem (s.gpr .rdx) =
    compress (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
  pub s t := s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩, ⟨0x4000, 4096⟩]

theorem compress_implies : compressLocal.Implies (compressContract X86_64.abi) := by
  sig_implies [compressContract, compressSig, compressLocal, X86_64.abi, X86_64.argRegs]
    [satState] using satState

end VG.Proof.Argon2.X86_64
