import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
import VerifiedGarbage.Proof.Ed25519.AArch64.PointFromScalar

/-! Untrusted: the scalars read for verification, and the public registers that read them. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def ScalarCTPre (count : Nat) (base k : Addr) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x1 = k ∧
    (∀ i < 2 * count, InRegions (s.rd ++ s.wr) (off k i) 1) ∧
    ∀ i < 2 * count, 8192 ≤ ofs base (off k i)

theorem scalarInput_agree {count : Nat} {base k : Addr} {s t : State}
    (h : ScalarCTPre count base k s ∧ ScalarCTPre count base k t) :
    ∀ r ∈ Taint.ofRegs [.x0, .x1], s.gpr r = t.gpr r := by
  apply agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.x0.trans h.2.1.x0.symm
  · exact h.1.2.1.trans h.2.2.1.symm

end VG.Proof.Ed25519.AArch64
