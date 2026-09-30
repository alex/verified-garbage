import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulCTLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMul

/-! Untrusted: complete secret scalar multiplication has a public trace. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def MulCTPreN (count : Nat) (base : Addr) (scalar : Nat) (s : State) : Prop :=
  Scr s base ∧ scalar < 2 ^ (16 * count) ∧ env s.mem base 16 = Spec.Ed25519.d ∧
    ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)

abbrev MulCTPre := MulCTPreN 16

theorem pointMultiply_ct_of_init (count : Nat) (base : Addr) (scalar₁ scalar₂ : Nat)
    (hn0 : 0 < count) (hn : count ≤ 32)
    (initCT : CT (fun x y => MulCTPreN count base scalar₁ x ∧ MulCTPreN count base scalar₂ y)
      (pointMultiplyInit count) (fun _ _ => True)) :
    CT (fun x y => MulCTPreN count base scalar₁ x ∧ MulCTPreN count base scalar₂ y)
      (pointMultiply count) (fun _ _ => True) := by
  have hi := withRuns initCT (fun x y h =>
    ⟨pointMultiplyInit_ok h.1.1 count scalar₁ hn0 hn h.1.2.1 h.1.2.2.1 h.1.2.2.2,
     pointMultiplyInit_ok h.2.1 count scalar₂ hn0 hn h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩)
  rw [pointMultiply]
  refine CT.seq hi ?_
  intro x y tx ty x' y' ⟨hsp, _, a, b, _, hx, hy⟩ ex ey
  exact pointMulLoop_ct a b base count scalar₁ scalar₂ _ _ hn count _ _ _ _ _ _ ⟨hsp, hx, hy⟩ ex ey

theorem pointMultiply16_ct (base : Addr) (scalar₁ scalar₂ : Nat) :
    CT (fun x y => MulCTPre base scalar₁ x ∧ MulCTPre base scalar₂ y)
      (pointMultiply 16) (fun _ _ => True) := by
  have initCT : CT (fun x y => MulCTPre base scalar₁ x ∧ MulCTPre base scalar₂ y)
      (pointMultiplyInit 16) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    intro x y h
    exact agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.x0.trans h.2.1.x0.symm)
  exact pointMultiply_ct_of_init 16 base scalar₁ scalar₂ (by decide) (by decide) initCT

end VG.Proof.Ed25519.AArch64
