import VerifiedGarbage.Impl.Ed25519.Arm.PointLoop
import VerifiedGarbage.Proof.Ed25519.Arm.Points
import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
import VerifiedGarbage.Proof.Ed25519.ScalarMul

/-! Untrusted: fixed batches of exact doublings preserve the saved accumulator. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem doubleBody_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (n : Nat) (hn : n < 16) (hcount : s.gpr .r10 = BitVec.ofNat 32 (n + 1))
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa doubleBody s fun t => t.gpr .r10 = BitVec.ofNat 32 n ∧ t.z = decide (n = 0) ∧
      AllLim t.mem b ∧ point (env t.mem b) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem b) 0 1 2 3) (point (env s.mem b) 0 1 2 3) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧ IKeep b s t := by
  refine WP.seq (WP.mono (pointDouble_ok hc hl hd) fun t ⟨hk, hlt, hv, hi⟩ => ?_)
  refine WP.mono (decR10_ok (by omega) ((hk.rest.gpr _ (by decide)).trans hcount))
    fun u ⟨hu, hz, hr, hm⟩ => ?_
  exact ⟨hu, hz, hm ▸ hlt, by rw [hm]; exact hv, by rw [hm]; exact hi,
    (IKeep.of_keep hk).trans (IKeep.of_counter hr hm)⟩

structure DoubleInv (s₀ : State) (b : BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  ctx : Ctx b s
  lim : AllLim s.mem b
  counter : s.gpr .r10 = BitVec.ofNat 32 n
  value : point (env s.mem b) 0 1 2 3 = powerPoint (point (env s₀.mem b) 0 1 2 3) (16 - n)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem b i = env s₀.mem b i
  keep : IKeep b s₀ s

theorem doubleLoop_ok {s₀ : State} {b : BitVec 32} (hc : Ctx b s₀) (hl : AllLim s₀.mem b)
    (hcount : s₀.gpr .r10 = 16) (hd : env s₀.mem b 16 = Spec.Ed25519.d) :
    WP isa (.loop doubleBody .ne) s₀ fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s₀.mem b) 0 1 2 3) 16 ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s₀.mem b i) ∧ IKeep b s₀ t := by
  apply WP.loop (DoubleInv s₀ b) (n := 16)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := hi.bound; omega
    refine WP.mono (doubleBody_ok hi.ctx hi.lim k hk hi.counter
      ((hi.high 16 (by decide)).trans hd)) fun t ⟨htc, htz, htl, htv, hthi, htk⟩ => ?_
    have hv : point (env t.mem b) 0 1 2 3 = powerPoint (point (env s₀.mem b) 0 1 2 3) (16 - k) := by
      rw [htv, hi.value, show 16 - k = (16 - (k + 1)) + 1 by omega, powerPoint]
    have hh : ∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s₀.mem b i :=
      fun i h => (hthi i h).trans (hi.high i h)
    have hkeep := hi.keep.trans htk
    by_cases hk0 : k = 0
    · subst hk0
      exact .inl ⟨by simp only [VG.Arm.eval, htz, decide_true, Bool.not_true], htl, hv, hh, hkeep⟩
    · exact .inr ⟨by simp only [VG.Arm.eval, htz, decide_eq_false hk0, Bool.not_false],
        k, by omega, ⟨by omega, by omega, htk.ctx hi.ctx, htl, htc, hv, hh, hkeep⟩⟩
  · exact ⟨by decide, by decide, hc, hl, hcount, rfl, fun _ _ => rfl,
      ⟨Rest.refl _ _, Frame.refl _ _⟩⟩

theorem double16_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b)
    (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa double16 s fun t => AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) 16 ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧ IKeep b s t := by
  refine WP.seq (wp_movw fun t ht => WP.block_nil ?_)
  have hk : IKeep b s t := IKeep.of_counter (ht.rest (by decide)) ht.mem
  refine WP.mono (doubleLoop_ok (hk.ctx hc) (by rw [ht.mem]; exact hl)
    ht.gpr (by rw [ht.mem]; exact hd)) fun u ⟨hlu, hv, hh, hu⟩ => ?_
  rw [ht.mem] at hv hh
  exact ⟨hlu, hv, hh, hk.trans hu⟩

end VG.Proof.Ed25519.Arm
