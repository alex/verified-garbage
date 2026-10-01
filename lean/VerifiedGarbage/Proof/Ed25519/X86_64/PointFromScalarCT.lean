import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCT
import VerifiedGarbage.Proof.Ed25519.X86_64.PointFromScalar

/-! Untrusted: the scalars read for verification, and the public registers that read them. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

def ScalarCTPre (count : Nat) (base k : Addr) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rsi = k ∧
    (∀ i < 2 * count, InRegions (s.rd ++ s.wr) (off k i) 1) ∧
    ∀ i < 2 * count, 8192 ≤ ofs base (off k i)

theorem scalarInput_agree {count : Nat} {base k : Addr} {s t : State}
    (h : ScalarCTPre count base k s ∧ ScalarCTPre count base k t) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rsi]) s t := by
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.rdi.trans h.2.1.rdi.symm
  · exact h.1.2.1.trans h.2.2.1.symm

end VG.Proof.Ed25519.X86_64
