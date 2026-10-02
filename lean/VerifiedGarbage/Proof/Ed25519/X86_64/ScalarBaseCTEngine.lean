import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCT
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseEngine

/-! Untrusted: expand secret scalar bits, multiply, and encode with a public trace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

variable {fld : Arith} [EdArith fld]

def BaseEnginePre (base k : Addr) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rsi = k ∧
    (∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1) ∧
    ∀ q < 32, 8192 ≤ ofs base (off k q)

end VG.Proof.Ed25519.X86_64
