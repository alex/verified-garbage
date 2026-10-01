import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTBody
import VerifiedGarbage.Proof.Ed25519.Arm.PointMulLoop

/-! Both runs descend through the same public checkpoint count. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem pointMulLoop_ct (s₁ s₂ : State) (b ptr : BitVec 32) (count scalar₁ scalar₂ : Nat)
    (p₁ p₂ : Spec.Ed25519.Point) (n : Nat) :
    CT (fun x y => PointMulInv s₁ b ptr count scalar₁ p₁ n x ∧
      PointMulInv s₂ b ptr count scalar₂ p₂ n y) (.loop pointMulBody .ne) (fun _ _ => True) := by
  apply RelCT.loop (M := isa) (fun n x y => PointMulInv s₁ b ptr count scalar₁ p₁ n x ∧
    PointMulInv s₂ b ptr count scalar₂ p₂ n y) _ n
  intro k
  cases k with
  | zero =>
    apply RelCT.of_false
    intro x y h
    exact Nat.not_lt_zero _ h.1.positive
  | succ j =>
    by_cases hj : j < count ∧ count ≤ 32
    · have hc := (pointMulBody_ct b ptr j (by omega)).mono
        (fun x y (h : PointMulInv s₁ b ptr count scalar₁ p₁ (j + 1) x ∧
            PointMulInv s₂ b ptr count scalar₂ p₂ (j + 1) y) =>
          ⟨⟨h.1.ctx, h.1.lim, h.1.input.pointer, h.1.counter, h.1.d⟩,
           ⟨h.2.ctx, h.2.lim, h.2.input.pointer, h.2.counter, h.2.d⟩⟩)
        (fun _ _ h => h)
      intro x y tx ty u v h ex ey
      have he := (hc _ _ _ _ _ _ h ex ey).1
      obtain ⟨_, u', eu, hu⟩ := pointMulBody_ok h.1.ctx h.1.lim count scalar₁ j p₁ h.1.input
        hj.1 h.1.d h.1.value h.1.counter (h.1.table j hj.1)
      obtain ⟨_, v', ev, hv⟩ := pointMulBody_ok h.2.ctx h.2.lim count scalar₂ j p₂ h.2.input
        hj.1 h.2.d h.2.value h.2.counter (h.2.table j hj.1)
      obtain ⟨_, rfl⟩ := Exec.det ex eu
      obtain ⟨_, rfl⟩ := Exec.det ey ev
      have ez : VG.Arm.eval .ne u = VG.Arm.eval .ne v := by
        simp only [VG.Arm.eval, hu.2.2.2.2.2, hv.2.2.2.2.2]
      refine ⟨he, ez, fun _ => trivial, ?_⟩
      intro hj0
      have hnz : j ≠ 0 := by
        intro hz
        subst j
        simp only [VG.Arm.eval, hu.2.2.2.2.2, decide_true, Bool.not_true] at hj0
        cases hj0
      refine ⟨j, by omega, ?_, ?_⟩
      · refine ⟨by omega, by omega, hu.1.ctx h.1.ctx, hu.2.1,
          h.1.input.keep hu.1 (by decide) (by decide), hu.2.2.2.2.1,
          hu.2.2.1, hu.2.2.2.1, ?_, h.1.keep.trans hu.1⟩
        intro i hi
        exact (hu.1.table (by omega) (by omega) (by decide) (.inl (by omega))).trans (h.1.table i hi)
      · refine ⟨by omega, by omega, hv.1.ctx h.2.ctx, hv.2.1,
          h.2.input.keep hv.1 (by decide) (by decide), hv.2.2.2.2.1,
          hv.2.2.1, hv.2.2.2.1, ?_, h.2.keep.trans hv.1⟩
        intro i hi
        exact (hv.1.table (by omega) (by omega) (by decide) (.inl (by omega))).trans (h.2.table i hi)
    · apply RelCT.of_false
      intro x y h
      have := h.1.bound
      have := h.1.input.bound
      omega

end VG.Proof.Ed25519.Arm
