import VerifiedGarbage.Proof.Ed25519.Arm.PointMulBody

/-! Untrusted: descending through every checkpoint proves the full scalar product. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure PointMulInv (s₀ : State) (b ptr : BitVec 32) (count scalar : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ count
  ctx : Ctx b s
  lim : AllLim s.mem b
  input : MulInput b ptr count scalar s
  counter : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 n
  d : env s.mem b 16 = Spec.Ed25519.d
  value : point (env s.mem b) 0 1 2 3 = after scalar p (16 * n)
  table : ∀ j < count, tablePoint s.mem b (1600 + 128 * j) = powerPoint p (16 * j)
  keep : MulKeep b 5696 2048 s₀ s

theorem pointMulLoop_ok {b ptr : BitVec 32} {s₀ : State} (hc : Ctx b s₀) (hl : AllLim s₀.mem b)
    (count scalar : Nat) (p : Spec.Ed25519.Point) (hi : MulInput b ptr count scalar s₀)
    (hn : 0 < count) (hd : env s₀.mem b 16 = Spec.Ed25519.d)
    (hp : point (env s₀.mem b) 0 1 2 3 = after scalar p (16 * count))
    (hcj : s₀.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 count)
    (ht : ∀ j < count, tablePoint s₀.mem b (1600 + 128 * j) = powerPoint p (16 * j)) :
    WP isa (.loop pointMulBody .ne) s₀ fun t => MulKeep b 5696 2048 s₀ t ∧ AllLim t.mem b ∧
      env t.mem b 16 = Spec.Ed25519.d ∧ point (env t.mem b) 0 1 2 3 = Spec.Ed25519.pointMul scalar p := by
  apply WP.loop (PointMulInv s₀ b ptr count scalar p) (n := count)
  · intro n s h
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hj : j < count := by have := h.bound; omega
    refine WP.mono (pointMulBody_ok h.ctx h.lim count scalar j p h.input hj h.d h.value h.counter
      (h.table j hj)) fun t ⟨tk, tl, td, tp, tc, tz⟩ => ?_
    have tt : ∀ i < count, tablePoint t.mem b (1600 + 128 * i) = powerPoint p (16 * i) := by
      intro i hib
      have := h.input.bound
      exact (tk.table (by omega) (by omega) (by decide) (.inl (by omega))).trans (h.table i hib)
    by_cases hj0 : j = 0
    · subst hj0
      exact .inl ⟨by simp only [VG.Arm.eval, tz, decide_true, Bool.not_true], h.keep.trans tk,
        tl, td, tp.trans (after_zero scalar p)⟩
    · exact .inr ⟨by simp only [VG.Arm.eval, tz, decide_eq_false hj0, Bool.not_false],
        j, by omega, ⟨by omega, by omega, tk.ctx h.ctx, tl,
          h.input.keep tk (by decide) (by decide), tc, td, tp, tt, h.keep.trans tk⟩⟩
  · exact ⟨hn, Nat.le_refl _, hc, hl, hi, hcj, hd, hp, ht, MulKeep.refl _ _ _ _⟩

end VG.Proof.Ed25519.Arm
