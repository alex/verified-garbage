import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul32CT
import VerifiedGarbage.Proof.Ed25519.X86_64.PointFromScalar

/-! Untrusted: the two scalar widths used in verification have public traces. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs)

def ScalarCTPre (count : Nat) (base k : Addr) (s : State) : Prop :=
  Scratch s base ∧ s.gpr .rsi = k ∧
    (∀ i < 2 * count, InRegions (s.rd ++ s.wr) (off k i) 1) ∧
    ∀ i < 2 * count, 8192 ≤ ofs base (off k i)

theorem pointFromScalar_ct_of (count : Nat) (base k : Addr) (hn0 : 0 < count) (hn : count ≤ 32)
    (hp : RelCT isa (fun s t => ScalarCTPre count base k s ∧ ScalarCTPre count base k t)
      (pointFromScalarPrepare count) (fun _ _ => True))
    (hm : ∀ a b, RelCT isa (fun s t => MulCTPreN count base a s ∧ MulCTPreN count base b t)
      (pointMultiply count) (fun _ _ => True)) :
    RelCT isa (fun s t => ScalarCTPre count base k s ∧ ScalarCTPre count base k t)
      (pointFromScalar count) (fun _ _ => True) := by
  have hp' := withRuns hp (fun s t h =>
    ⟨pointFromScalarPrepare_ok h.1.1 h.1.2.1 count hn0 hn h.1.2.2.1 h.1.2.2.2,
     pointFromScalarPrepare_ok h.2.1 h.2.2.1 count hn0 hn h.2.2.2.1 h.2.2.2.2⟩)
  rw [pointFromScalar]
  refine VG.RelCT.seq hp' ?_
  intro s t ts tt s' t' ⟨_, a, b, hab, ha, hb⟩ es et
  exact hm (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt a.mem k (2 * count)))
    (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt b.mem k (2 * count))) _ _ _ _ _ _
    ⟨⟨ha.1.scratch hab.1.1, ha.2.2.2.1, ha.2.2.1, ha.2.2.2.2⟩,
      ⟨hb.1.scratch hab.2.1, hb.2.2.2.1, hb.2.2.1, hb.2.2.2.2⟩⟩ es et

theorem scalarInput_agree {count : Nat} {base k : Addr} {s t : State}
    (h : ScalarCTPre count base k s ∧ ScalarCTPre count base k t) :
    VG.X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rsi]) s t := by
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.rdi.trans h.2.1.rdi.symm
  · exact h.1.2.1.trans h.2.2.1.symm

theorem pointFromScalar16_ct (base k : Addr) :
    RelCT isa (fun s t => ScalarCTPre 16 base k s ∧ ScalarCTPre 16 base k t)
      (pointFromScalar 16) (fun _ _ => True) := by
  apply pointFromScalar_ct_of 16 base k (by decide) (by decide) _ (pointMultiply16_ct base)
  apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi]) _ (by taint_decide)
  exact fun _ _ h => scalarInput_agree h

theorem pointFromScalar32_ct (base k : Addr) :
    RelCT isa (fun s t => ScalarCTPre 32 base k s ∧ ScalarCTPre 32 base k t)
      (pointFromScalar 32) (fun _ _ => True) := by
  apply pointFromScalar_ct_of 32 base k (by decide) (by decide) _ (pointMultiply32_ct base)
  apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi]) _ (by taint_decide)
  exact fun _ _ h => scalarInput_agree h

end VG.Proof.Ed25519.X86_64
