import VerifiedGarbage.Proof.Ed25519.X86.PointPowers

/-! Checkpoint-loop termination and the exact contents of every entry. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure PowersInv (s₀ : State) (x : BitVec 32) (o count n : Nat) (batch : Bool) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ count
  scratch : Ctx x s
  counter : wd s.mem x 24 = BitVec.ofNat 32 (count - n)
  value : point (env s.mem x) 0 1 2 3 =
    powerPoint (point (env s₀.mem x) 0 1 2 3) (powerStride batch * (count - n))
  table : ∀ j < count - n, tablePoint s.mem x (o + 128 * j) =
    powerPoint (point (env s₀.mem x) 0 1 2 3) (powerStride batch * j)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem x i = env s₀.mem x i
  keep : PowersKeep x o (128 * count) s₀ s

theorem powersLoop_ok (batch : Bool) {s₀ : State} {x : BitVec 32} (hc : Ctx x s₀)
    (o count : Nat) (hlo : 928 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hn0 : 0 < count) (hn : count ≤ 32) (hcounter : wd s₀.mem x 24 = 0)
    (hd : env s₀.mem x 16 = Spec.Ed25519.d) :
    WP isa (.loop (powersBody o count batch) .ne) s₀ fun t =>
      PowersKeep x o (128 * count) s₀ t ∧
      (∀ j < count, tablePoint t.mem x (o + 128 * j) =
        powerPoint (point (env s₀.mem x) 0 1 2 3) (powerStride batch * j)) ∧
      point (env t.mem x) 0 1 2 3 =
        powerPoint (point (env s₀.mem x) 0 1 2 3) (powerStride batch * count) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s₀.mem x i := by
  apply WP.loop (fun n => PowersInv s₀ x o count n batch) (n := count)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < count := by have := hi.bound; omega
    refine WP.mono (powersBody_ok hi.scratch o count (count - (k + 1)) batch (by omega) hn hlo hbound
      hi.counter ((hi.high 16 (by decide)).trans hd)) fun t ⟨kt, it, zt, pt, tt, ht⟩ => ?_
    have hstep : count - (k + 1) + 1 = count - k := by omega
    have pv : point (env t.mem x) 0 1 2 3 =
        powerPoint (point (env s₀.mem x) 0 1 2 3) (powerStride batch * (count - k)) := by
      rw [pt, hi.value, ← powerPoint_add]
      exact congrArg (powerPoint _) (by rw [← hstep, Nat.mul_add, Nat.mul_one])
    have tv : ∀ j < count - k, tablePoint t.mem x (o + 128 * j) =
        powerPoint (point (env s₀.mem x) 0 1 2 3) (powerStride batch * j) := by
      intro j hj
      by_cases hj' : j < count - (k + 1)
      · rw [kt.frame.table hc.fit (by omega) (by omega) (by omega) (Or.inl (by omega)), hi.table j hj']
      · have he : j = count - (k + 1) := by omega
        rw [he, tt, hi.value]
    have hh : ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s₀.mem x i :=
      fun i h => (ht i h).trans (hi.high i h)
    have kk := hi.keep.trans (kt.mono hi.scratch (by omega) (by omega) (by omega))
    by_cases hk0 : k = 0
    · subst k
      exact .inl ⟨by rw [zt, show count - (0 + 1) + 1 = count by omega]; simp, kk, tv, pv, hh⟩
    · exact .inr ⟨by rw [zt]; simp only [show count - (k + 1) + 1 ≠ count by omega, decide_false]; rfl,
        k, by omega, ⟨by omega, by omega, kt.ctx hi.scratch, hstep ▸ it, pv, tv, hh, kk⟩⟩
  · refine ⟨hn0, Nat.le_refl _, hc, ?_, ?_, ?_, fun _ _ => rfl, PowersKeep.refl _ _ _ _⟩
    · rw [Nat.sub_self]; exact hcounter
    · simp only [Nat.sub_self, Nat.mul_zero, powerPoint]
    · intro j hj; omega

theorem pointPowers_ok (batch : Bool) {s : State} {x : BitVec 32} (hc : Ctx x s)
    (o count : Nat) (hlo : 928 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hn0 : 0 < count) (hn : count ≤ 32) (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (pointPowers o count batch) s fun t =>
      PowersKeep x o (128 * count) s t ∧
      (∀ j < count, tablePoint t.mem x (o + 128 * j) =
        powerPoint (point (env s.mem x) 0 1 2 3) (powerStride batch * j)) ∧
      point (env t.mem x) 0 1 2 3 =
        powerPoint (point (env s.mem x) 0 1 2 3) (powerStride batch * count) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem x i = env s.mem x i := by
  refine WP.seq (WP.mono (powersInit_ok hc o (128 * count)) fun t ⟨kt, it, ft⟩ => ?_)
  have et := counter_env hc.fit ft
  refine WP.mono (powersLoop_ok batch (kt.ctx hc) o count hlo hbound hn0 hn it
    (by rw [et]; exact hd)) fun u ⟨ku, tu, pu, hu⟩ => ?_
  rw [et] at tu pu hu
  exact ⟨kt.trans ku, tu, pu, hu⟩

end VG.Proof.Ed25519.X86
