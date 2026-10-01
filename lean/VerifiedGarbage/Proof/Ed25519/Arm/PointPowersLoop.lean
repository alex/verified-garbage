import VerifiedGarbage.Proof.Ed25519.Arm.PointPowers

/-! Untrusted: checkpoint-loop termination and exact table contents. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure PowersInv (s₀ : State) (b : BitVec 32) (o count n : Nat) (batch : Bool) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ count
  ctx : Ctx b s
  lim : AllLim s.mem b
  counter : s.gpr .r11 = BitVec.ofNat 32 (count - n)
  value : point (env s.mem b) 0 1 2 3 =
    powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * (count - n))
  table : ∀ j < count - n, tablePoint s.mem b (o + 128 * j) =
    powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * j)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem b i = env s₀.mem b i
  keep : PowersKeep b o (128 * count) s₀ s

theorem powersLoop_ok (batch : Bool) {s₀ : State} {b : BitVec 32} (hc : Ctx b s₀)
    (hl : AllLim s₀.mem b) (o count : Nat) (hlo : 1600 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hn0 : 0 < count) (hn : count ≤ 32) (h11 : s₀.gpr .r11 = 0)
    (hd : env s₀.mem b 16 = Spec.Ed25519.d) :
    WP isa (.loop (powersBody o count batch) .ne) s₀ fun t => AllLim t.mem b ∧
      (∀ j < count, tablePoint t.mem b (o + 128 * j) =
        powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * j)) ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * count) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s₀.mem b i) ∧
      PowersKeep b o (128 * count) s₀ t := by
  apply WP.loop (fun n => PowersInv s₀ b o count n batch) (n := count)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < count := by have := hi.bound; omega
    refine WP.mono (powersBody_ok batch hi.ctx hi.lim o (count - (k + 1)) count hlo hbound
      (by omega) hn hi.counter ((hi.high 16 (by decide)).trans hd))
      fun t ⟨htc, htz, htl, htt, htv, hthi, htk⟩ => ?_
    have hstep : count - (k + 1) + 1 = count - k := by omega
    have hv : point (env t.mem b) 0 1 2 3 =
        powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * (count - k)) := by
      rw [htv, hi.value, ← powerPoint_add]
      exact congrArg (powerPoint _) (by
        cases batch <;> simp only [powerStride, Bool.false_eq_true, ite_true, ite_false] <;> omega)
    have ht : ∀ j < count - k, tablePoint t.mem b (o + 128 * j) =
        powerPoint (point (env s₀.mem b) 0 1 2 3) (powerStride batch * j) := by
      intro j hj
      by_cases h : j < count - (k + 1)
      · rw [TableFrame.point htk.frame (by omega) (.inl (by omega)) (by omega) (by omega), hi.table j h]
      · have he : j = count - (k + 1) := by omega
        rw [he, htt, hi.value]
    have hh : ∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s₀.mem b i :=
      fun i h => (hthi i h).trans (hi.high i h)
    have hkeep := hi.keep.trans (htk.mono (by omega) (by omega))
    by_cases hk0 : k = 0
    · subst hk0
      exact .inl ⟨by simp only [VG.Arm.eval, htz, show count - (0 + 1) + 1 = count by omega,
        decide_true, Bool.not_true], htl, ht, hv, hh, hkeep⟩
    · exact .inr ⟨by simp only [VG.Arm.eval, htz,
        decide_eq_false (show count - (k + 1) + 1 ≠ count by omega), Bool.not_false],
        k, by omega, ⟨by omega, by omega, htk.ctx hi.ctx, htl, hstep ▸ htc, hv, ht, hh, hkeep⟩⟩
  · refine ⟨hn0, Nat.le_refl _, hc, hl, ?_, ?_, ?_, fun _ _ => rfl, PowersKeep.refl _ _ _ _⟩
    · rw [Nat.sub_self]; exact h11
    · simp only [Nat.sub_self, Nat.mul_zero, powerPoint]
    · intro j hj; omega

theorem pointPowers_ok (batch : Bool) {s : State} {b : BitVec 32} (hc : Ctx b s)
    (hl : AllLim s.mem b) (o count : Nat) (hlo : 1600 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hn0 : 0 < count) (hn : count ≤ 32) (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa (pointPowers o count batch) s fun t => AllLim t.mem b ∧
      (∀ j < count, tablePoint t.mem b (o + 128 * j) =
        powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch * j)) ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch * count) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ∧ PowersKeep b o (128 * count) s t := by
  refine WP.seq (wp_movw fun t ht => WP.block_nil ?_)
  have hr : Rest [.r11] s t := ht.rest (by decide)
  refine WP.mono (powersLoop_ok batch (hc.of_rest hr (by decide)) (by rw [ht.mem]; exact hl)
    o count hlo hbound hn0 hn ht.gpr (by rw [ht.mem]; exact hd)) fun u ⟨hlu, htu, hv, hh, hu⟩ => ?_
  have hkeep : PowersKeep b o (128 * count) s t :=
    ⟨hr.mono (by decide), by rw [ht.mem]; exact Frame.refl _ _⟩
  rw [ht.mem] at htu hv hh
  exact ⟨hlu, htu, hv, hh, hkeep.trans hu⟩

end VG.Proof.Ed25519.Arm
