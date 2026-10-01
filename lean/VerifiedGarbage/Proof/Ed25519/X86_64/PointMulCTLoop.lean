import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulLoop

/-! Untrusted: both executions descend through the same public checkpoint count. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]

theorem pointMulLoop_ct (s₁ s₂ : State) (base : Addr) (count scalar₁ scalar₂ : Nat)
    (p₁ p₂ : Spec.Ed25519.Point) (hn : count ≤ 32) (n : Nat) :
    RelCT isa (fun x y => PointMulInv s₁ base count scalar₁ p₁ n x ∧
      PointMulInv s₂ base count scalar₂ p₂ n y) (.loop (pointMulBatch fld) .ne) (fun _ _ => True) := by
  apply VG.RelCT.loop (M := isa) (fun n x y => PointMulInv s₁ base count scalar₁ p₁ n x ∧
    PointMulInv s₂ base count scalar₂ p₂ n y) _ n
  intro k
  cases k with
  | zero =>
    apply VG.RelCT.of_false
    intro x y h
    exact Nat.not_lt_zero _ h.1.positive
  | succ j =>
    by_cases hj : j < count
    · have hct := (pointMulBatch_ct (fld := fld) base j (by omega)).mono
        (fun x y (h : PointMulInv s₁ base count scalar₁ p₁ (j + 1) x ∧
            PointMulInv s₂ base count scalar₂ p₂ (j + 1) y) =>
          ⟨⟨h.1.scratch, h.1.counter, h.1.d⟩, ⟨h.2.scratch, h.2.counter, h.2.d⟩⟩)
        (fun _ _ h => h)
      have hw := withRuns hct (fun x y h =>
        ⟨pointMulBatch_ok h.1.scratch j count scalar₁ p₁ hj hn h.1.counter h.1.d h.1.value h.1.bits h.1.table,
         pointMulBatch_ok h.2.scratch j count scalar₂ p₂ hj hn h.2.counter h.2.d h.2.value h.2.bits h.2.table⟩)
      refine hw.mono (fun _ _ h => h) ?_
      intro x y ⟨_, a, b, hi, hx, hy⟩
      have ex : eval .ne x = some (!(decide (j = 0))) := by
        simp only [eval, hx.2.1, Option.map_some]
      have ey : eval .ne y = some (!(decide (j = 0))) := by
        simp only [eval, hy.2.1, Option.map_some]
      refine ⟨ex.trans ey.symm, fun _ => trivial, ?_⟩
      intro he
      have hj0 : j ≠ 0 := by
        intro hz
        subst j
        simp only [ex, decide_true, Bool.not_true] at he
        cases he
      refine ⟨j, by omega, ?_, ?_⟩
      · exact ⟨by omega, by omega, hx.2.2.2.2.2.2.scratch hi.1.scratch, hx.1,
          hx.2.2.2.1, hx.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1,
          hi.1.keep.trans hx.2.2.2.2.2.2⟩
      · exact ⟨by omega, by omega, hy.2.2.2.2.2.2.scratch hi.2.scratch, hy.1,
          hy.2.2.2.1, hy.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1,
          hi.2.keep.trans hy.2.2.2.2.2.2⟩
    · apply VG.RelCT.of_false
      intro x y h
      have := h.1.bound
      omega

end VG.Proof.Ed25519.X86_64
