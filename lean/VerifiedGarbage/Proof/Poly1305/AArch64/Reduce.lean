import VerifiedGarbage.Proof.Poly1305.AArch64.Absorb

/-!
# Poly1305 on AArch64: the final reduction

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P)

/-- `h` reduced fully, into normalized limbs. -/
theorem reduce_ok (s : State) (hm : s.gpr .x17 = M26) :
    WP isa (.block reduce) s fun s' =>
      (Bounds s → Norm (hv s) (v s' .x4) (v s' .x5) (v s' .x6) (v s' .x7) (v s' .x8)) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15] s s' := by
  rw [reduce]
  refine WP.block_append (WP.mono (reduceA_ok s hm) fun s₁ ⟨h₁, k₁⟩ => ?_)
  refine WP.mono (select_ok s₁) fun s₂ ⟨c4, c5, c6, c7, c8, k₂⟩ => ⟨fun ⟨b0, b1, b2, b3, b4⟩ => ?_,
    (k₁.trans k₂).mono (by decide)⟩
  rcases h₁ b0 b1 b2 b3 b4 with ⟨hz, hn⟩ | ⟨ho, hn⟩
  · have hz := eq_zero_of_toNat hz
    simp only [v, c4, c5, c6, c7, c8, hz, select_zero]
    exact hn
  · have ho := eq_ones_of_toNat ho
    simp only [v, c4, c5, c6, c7, c8, ho, select_ones]
    exact hn

end VG.Proof.Poly1305.AArch64
