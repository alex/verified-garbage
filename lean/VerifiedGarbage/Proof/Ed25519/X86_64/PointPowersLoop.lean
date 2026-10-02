import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers

/-! Termination and table contents for the checkpoint loop. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

variable {fld : Arith} [EdArith fld]

structure PowersInv (s₀ : State) (base : Addr) (o count n : Nat) (batch : Bool) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ count
  scratch : Scratch s base
  counter : s.gpr .rbx = BitVec.ofNat 64 (count - n)
  value : point (env s.mem base) 0 1 2 3 = powerPoint (point (env s₀.mem base) 0 1 2 3) (powerStride batch * (count - n))
  table : ∀ j < count - n, tablePoint s.mem base (o + 128 * j) =
    powerPoint (point (env s₀.mem base) 0 1 2 3) (powerStride batch * j)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem base i = env s₀.mem base i
  keep : PowersKeep base o (128 * count) s₀ s

theorem powersLoop_ok (batch : Bool) {s₀ : State} {base : Addr} (hs : Scratch s₀ base)
    (o count : Nat) (hlo : 768 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hn0 : 0 < count) (hn : count ≤ 32) (hc : s₀.gpr .rbx = 0)
    (hd : env s₀.mem base 16 = Spec.Ed25519.d) :
    WP isa (.loop (powersBody fld o count batch) .ne) s₀ fun t =>
      (∀ j < count, tablePoint t.mem base (o + 128 * j) =
        powerPoint (point (env s₀.mem base) 0 1 2 3) (powerStride batch * j)) ∧
      point (env t.mem base) 0 1 2 3 = powerPoint (point (env s₀.mem base) 0 1 2 3) (powerStride batch * count) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s₀.mem base i) ∧
      PowersKeep base o (128 * count) s₀ t := by
  apply WP.loop (fun n => PowersInv s₀ base o count n batch) (n := count)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < count := by have := hi.bound; omega
    refine WP.mono (powersBody_ok batch hi.scratch o (count - (k + 1)) count hlo hbound (by omega) hn
      hi.counter ((hi.high 16 (by decide)).trans hd)) fun t ⟨htc, htz, htt, htv, hthi, htk⟩ => ?_
    have hstep : count - (k + 1) + 1 = count - k := by omega
    have hv : point (env t.mem base) 0 1 2 3 =
        powerPoint (point (env s₀.mem base) 0 1 2 3) (powerStride batch * (count - k)) := by
      rw [htv, hi.value, ← powerPoint_add]
      exact congrArg (powerPoint _) (by cases batch <;> simp only [powerStride, Bool.false_eq_true, ite_true, ite_false] <;> omega)
    have ht : ∀ j < count - k, tablePoint t.mem base (o + 128 * j) =
        powerPoint (point (env s₀.mem base) 0 1 2 3) (powerStride batch * j) := by
      intro j hj
      by_cases h : j < count - (k + 1)
      · rw [htk.mem.point (by omega) (Or.inl (by omega)) (by omega), hi.table j h]
      · have he : j = count - (k + 1) := by omega
        rw [he, htt, hi.value]
    have hh : ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s₀.mem base i :=
      fun i h => (hthi i h).trans (hi.high i h)
    have hkeep := hi.keep.trans (htk.mono (by omega) (by omega))
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, htz, show count - (0 + 1) + 1 = count by omega,
        decide_true, Option.map_some, Bool.not_true], ht, hv, hh, hkeep⟩
    · exact Or.inr ⟨by simp only [eval, htz,
        decide_eq_false (show count - (k + 1) + 1 ≠ count by omega), Option.map_some, Bool.not_false],
        k, by omega, ⟨by omega, by omega, htk.scratch hi.scratch, hstep ▸ htc, hv, ht, hh, hkeep⟩⟩
  · refine ⟨hn0, Nat.le_refl _, hs, ?_, ?_, ?_, fun _ _ => rfl, PowersKeep.refl _ _ _ _⟩
    · rw [Nat.sub_self]; exact hc
    · simp only [Nat.sub_self, Nat.mul_zero, powerPoint]
    · intro j hj; omega

theorem powersInit_ok (s : State) :
    WP isa (.block [.mov32 .rbx (.imm 0)]) s fun t => t.gpr .rbx = 0 ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem pointPowers_ok (batch : Bool) {s : State} {base : Addr} (hs : Scratch s base)
    (o count : Nat) (hlo : 768 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hn0 : 0 < count) (hn : count ≤ 32) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (pointPowers fld o count batch) s fun t =>
      (∀ j < count, tablePoint t.mem base (o + 128 * j) =
        powerPoint (point (env s.mem base) 0 1 2 3) (powerStride batch * j)) ∧
      point (env t.mem base) 0 1 2 3 = powerPoint (point (env s.mem base) 0 1 2 3) (powerStride batch * count) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧
      PowersKeep base o (128 * count) s t := by
  rw [pointPowers]
  refine WP.seq (WP.mono (powersInit_ok s) fun t ⟨hc, hk⟩ => ?_)
  refine WP.mono (powersLoop_ok batch (hs.of_keeps hk (by decide)) o count hlo hbound hn0 hn hc
    (by rw [hk.2.1]; exact hd)) fun u ⟨ht, hv, hh, hu⟩ => ?_
  have hkeep : PowersKeep base o (128 * count) s t := ⟨fun r hr _ _ => hk.1 r (by simpa using hr),
    hk.2.2.1, hk.2.2.2, by rw [hk.2.1]; exact TableFrame.refl _ _ _ _⟩
  rw [hk.2.1] at ht hv hh
  exact ⟨ht, hv, hh, hkeep.trans hu⟩

end VG.Proof.Ed25519.X86_64
