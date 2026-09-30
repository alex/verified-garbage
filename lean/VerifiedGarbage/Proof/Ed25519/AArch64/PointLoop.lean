import VerifiedGarbage.Impl.Ed25519.AArch64.PointLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.Points
import VerifiedGarbage.Proof.Ed25519.ScalarMul

/-! Untrusted: sixteen exact doublings, preserving the saved accumulator. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


structure DoubleKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x1 → r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 704 s.mem t.mem

theorem DoubleKeep.refl (base : Addr) (s : State) : DoubleKeep base s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem DoubleKeep.trans {base : Addr} {s t u : State} (h : DoubleKeep base s t)
    (k : DoubleKeep base t u) : DoubleKeep base s u :=
  ⟨fun r hr hc => (k.gpr r hr hc).trans (h.gpr r hr hc), k.rd.trans h.rd,
    k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem DoubleKeep.scratch {base : Addr} {s t : State} (h : DoubleKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem point_counter_nonzero : ∀ n < 16,
    (BitVec.ofNat 64 n != 0) = decide (n ≠ 0) := by decide

theorem doubleDec_ok (s : State) (n : Nat)
    (hc : s.gpr .x1 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x .x1 .x1 1]) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 n ∧ Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem doubleBody_ok {s : State} {base : Addr} (hs : Scr s base) (n : Nat)
    (hc : s.gpr .x1 = BitVec.ofNat 64 (n + 1)) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block doubleBody) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 n ∧
      point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) (point (env s.mem base) 0 1 2 3) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  rw [doubleBody, WP.block_append_iff]
  refine WP.mono (pointDouble_ok hs hd) fun t ⟨hk, hv, hi⟩ => ?_
  refine WP.mono (doubleDec_ok t n ((hk.gpr _ (by decide)).trans hc)) fun u ⟨hcu, ku⟩ => ?_
  refine ⟨hcu, ?_, ?_, ?_⟩
  · rw [ku.mem]; exact hv
  · rw [ku.mem]; exact hi
  · exact ⟨fun r hr hc => (ku.gpr r (by simpa using hr)).trans (hk.gpr r hc),
      ku.rd.trans hk.rd, ku.wr.trans hk.wr, ku.sp.trans hk.sp, by rw [ku.mem]; exact hk.mem⟩

structure DoubleInv (s₀ : State) (base : Addr) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  scratch : Scr s base
  counter : s.gpr .x1 = BitVec.ofNat 64 n
  value : point (env s.mem base) 0 1 2 3 =
    powerPoint (point (env s₀.mem base) 0 1 2 3) (16 - n)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem base i = env s₀.mem base i
  keep : DoubleKeep base s₀ s

theorem doubleLoop_ok {s₀ : State} {base : Addr} (hs : Scr s₀ base)
    (hc : s₀.gpr .x1 = 16) (hd : env s₀.mem base 16 = Spec.Ed25519.d) :
    WP isa (.loop (.block doubleBody) (.nonzero .x .x1)) s₀ fun t =>
      point (env t.mem base) 0 1 2 3 = powerPoint (point (env s₀.mem base) 0 1 2 3) 16 ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s₀.mem base i) ∧ DoubleKeep base s₀ t := by
  apply WP.loop (DoubleInv s₀ base) (n := 16)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := hi.bound; omega
    refine WP.mono (doubleBody_ok hi.scratch k hi.counter
      ((hi.high 16 (by decide)).trans hd)) fun t ⟨htc, htv, hthi, htk⟩ => ?_
    have hv : point (env t.mem base) 0 1 2 3 = powerPoint (point (env s₀.mem base) 0 1 2 3) (16 - k) := by
      rw [htv, hi.value, show 16 - k = (16 - (k + 1)) + 1 by omega, powerPoint]
    have hh : ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s₀.mem base i :=
      fun i h => (hthi i h).trans (hi.high i h)
    have hkeep := hi.keep.trans htk
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, read_x, htc, point_counter_nonzero 0 (by decide), show decide ((0 : Nat) ≠ 0) = false from rfl], hv, hh, hkeep⟩
    · exact Or.inr ⟨by simp only [eval, read_x, htc, point_counter_nonzero k hk, decide_eq_true hk0],
        k, by omega, ⟨by omega, by omega, htk.scratch hi.scratch, htc, hv, hh, hkeep⟩⟩
  · exact ⟨by decide, by decide, hs, hc, rfl, fun _ _ => rfl, DoubleKeep.refl _ _⟩

theorem doubleInit_ok (s : State) :
    WP isa (.block [.movz .w .x1 16 0]) s fun t => t.gpr .x1 = 16 ∧ Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem double16_ok {s : State} {base : Addr} (hs : Scr s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa double16 s fun t =>
      point (env t.mem base) 0 1 2 3 = powerPoint (point (env s.mem base) 0 1 2 3) 16 ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  rw [double16]
  refine WP.seq (WP.mono (doubleInit_ok s) fun t ⟨hc, hk⟩ => ?_)
  have hs' : Scr t base := ⟨(hk.gpr _ (by decide)).trans hs.x0, hk.wr ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (doubleLoop_ok hs' hc (by rw [hk.mem]; exact hd)) fun u ⟨hv, hh, hu⟩ => ?_
  have hkeep : DoubleKeep base s t := ⟨fun r hr _ => hk.gpr r (by simpa using hr),
    hk.rd, hk.wr, hk.sp, by rw [hk.mem]; exact Outside.refl _ _ _ _⟩
  rw [hk.mem] at hv hh
  exact ⟨hv, hh, hkeep.trans hu⟩

end VG.Proof.Ed25519.AArch64
