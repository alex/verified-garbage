import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul

/-! Untrusted: complete secret scalar multiplication has a public trace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

def MulCTPre (base : Addr) (scalar : Nat) (s : State) : Prop :=
  Scratch s base ∧ scalar < 2 ^ (16 * 16) ∧ env s.mem base 16 = Spec.Ed25519.d ∧
    ∀ i < 16 * 16, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)

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
  have hi := withRuns initCT (fun x y h =>
    ⟨pointMultiplyInit_ok h.1.1 16 scalar₁ (by decide) (by decide) h.1.2.1 h.1.2.2.1 h.1.2.2.2,
     pointMultiplyInit_ok h.2.1 16 scalar₂ (by decide) (by decide) h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩)
  rw [pointMultiply]
  refine VG.RelCT.seq hi ?_
  intro x y tx ty x' y' ⟨_, a, b, _, hx, hy⟩ ex ey
  exact pointMulLoop_ct a b base 16 scalar₁ scalar₂ _ _ (by decide) 16 _ _ _ _ _ _ ⟨hx, hy⟩ ex ey

end VG.Proof.Ed25519.X86_64
