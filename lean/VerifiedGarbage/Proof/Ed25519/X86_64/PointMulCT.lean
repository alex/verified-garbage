import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul

/-! Untrusted: complete secret scalar multiplication has a public trace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

def MulCTPreN (count : Nat) (base : Addr) (scalar : Nat) (s : State) : Prop :=
  Scratch s base ∧ scalar < 2 ^ (16 * count) ∧ env s.mem base 16 = Spec.Ed25519.d ∧
    ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)

abbrev MulCTPre := MulCTPreN 16

theorem pointMultiply_ct_of_init (count : Nat) (base : Addr) (scalar₁ scalar₂ : Nat)
    (hn0 : 0 < count) (hn : count ≤ 32)
    (initCT : RelCT isa (fun x y => MulCTPreN count base scalar₁ x ∧ MulCTPreN count base scalar₂ y)
      (pointMultiplyInit count) (fun _ _ => True)) :
    RelCT isa (fun x y => MulCTPreN count base scalar₁ x ∧ MulCTPreN count base scalar₂ y)
      (pointMultiply count) (fun _ _ => True) := by
  have hi := withRuns initCT (fun x y h =>
    ⟨pointMultiplyInit_ok h.1.1 count scalar₁ hn0 hn h.1.2.1 h.1.2.2.1 h.1.2.2.2,
     pointMultiplyInit_ok h.2.1 count scalar₂ hn0 hn h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩)
  rw [pointMultiply]
  refine VG.RelCT.seq hi ?_
  intro x y tx ty x' y' ⟨_, a, b, _, hx, hy⟩ ex ey
  exact pointMulLoop_ct a b base count scalar₁ scalar₂ _ _ hn count _ _ _ _ _ _ ⟨hx, hy⟩ ex ey

theorem pointMultiply16_ct (base : Addr) (scalar₁ scalar₂ : Nat) :
    RelCT isa (fun x y => MulCTPre base scalar₁ x ∧ MulCTPre base scalar₂ y)
      (pointMultiply 16) (fun _ _ => True) := by
  have initCT : RelCT isa (fun x y => MulCTPre base scalar₁ x ∧ MulCTPre base scalar₂ y)
      (pointMultiplyInit 16) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (Taint.ofRegs [.rdi]) _ (by taint_decide)
    intro x y h
    exact Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.rdi.trans h.2.1.rdi.symm)
  exact pointMultiply_ct_of_init 16 base scalar₁ scalar₂ (by decide) (by decide) initCT

end VG.Proof.Ed25519.X86_64
