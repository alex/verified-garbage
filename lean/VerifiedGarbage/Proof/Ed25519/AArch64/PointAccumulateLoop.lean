import VerifiedGarbage.Impl.Ed25519.AArch64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.PointAccumulate

/-! Untrusted: the descending-bit loop follows the specification exactly. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem accumulateDec_ok (s : State) (n : Nat)
    (hc : s.gpr .x19 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x .x19 .x19 1]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 n ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem accumulateBody_ok {s : State} {base : Addr} (hs : Scr s base)
    (n start scalar : Nat) (p : Spec.Ed25519.Point) (hn : n < 16) (hi : start + n < 512)
    (hc : s.gpr .x19 = BitVec.ofNat 64 (n + 1)) (hstart : s.gpr .x1 = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + n))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + n)) % 2))
    (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hp : point (env s.mem base) 0 1 2 3 = after scalar p (start + n + 1))
    (ht : tablePoint s.mem base (5376 + 128 * n) = powerPoint p (start + n)) :
    WP isa (.block accumulateBody) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 n ∧
      point (env t.mem base) 0 1 2 3 = after scalar p (start + n) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ CounterKeep base s t := by
  rw [accumulateBody, WP.block_append_iff]
  refine WP.mono (accumulateDec_ok s n hc) fun a ⟨ac, ka⟩ => ?_
  refine WP.mono (pointAccumulate_ok (hs.of_keeps ka (by decide)) n start ((scalar / 2 ^ (start + n)) % 2) hn hi (by omega) ac
    ((ka.gpr _ (by decide)).trans hstart) (by rw [ka.mem]; exact hb) (by rw [ka.mem]; exact hd))
    fun b ⟨kb, bp, bd⟩ => ?_
  have bc : b.gpr .x19 = BitVec.ofNat 64 n := (kb.gpr _ (by decide)).trans ac
  refine ⟨bc, ?_, bd, (CounterKeep.of_keeps ka (by decide)).trans (CounterKeep.of_keep kb)⟩
  rw [bp, ka.mem, hp, ht, ← after_step]

structure AccumulateInv (s₀ : State) (base : Addr) (start scalar : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  scratch : Scr s base
  counter : s.gpr .x19 = BitVec.ofNat 64 n
  startReg : s.gpr .x1 = BitVec.ofNat 64 start
  d : env s.mem base 16 = Spec.Ed25519.d
  value : point (env s.mem base) 0 1 2 3 = after scalar p (start + n)
  bits : ∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2)
  table : ∀ i < 16, tablePoint s.mem base (5376 + 128 * i) = powerPoint p (start + i)
  keep : CounterKeep base s₀ s

theorem CounterKeep.refl (base : Addr) (s : State) : CounterKeep base s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem accumulateLoop_ok {s₀ : State} {base : Addr} (hs : Scr s₀ base)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (hi : start + 16 ≤ 512)
    (hc : s₀.gpr .x19 = 16) (hstart : s₀.gpr .x1 = BitVec.ofNat 64 start)
    (hb : ∀ i < 16, s₀.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2))
    (hd : env s₀.mem base 16 = Spec.Ed25519.d)
    (hp : point (env s₀.mem base) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, tablePoint s₀.mem base (5376 + 128 * i) = powerPoint p (start + i)) :
    WP isa (.loop (.block accumulateBody) (.nonzero .x .x19)) s₀ fun t =>
      point (env t.mem base) 0 1 2 3 = after scalar p start ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ CounterKeep base s₀ t := by
  apply WP.loop (AccumulateInv s₀ base start scalar p) (n := 16)
  · intro n s h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := h.bound; omega
    refine WP.mono (accumulateBody_ok h.scratch k start scalar p hk (by omega) h.counter h.startReg
      (h.bits k hk) h.d (by rw [Nat.add_assoc]; exact h.value) (h.table k hk))
      fun t ⟨tc, tv, td, tk⟩ => ?_
    have hb' : ∀ i < 16, t.mem (off base (768 + (start + i))) =
        BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2) := by
      intro i hi'
      rw [tk.mem _ (by rw [ofs_off' base (by omega)]; omega), h.bits i hi']
    have ht' : ∀ i < 16, tablePoint t.mem base (5376 + 128 * i) = powerPoint p (start + i) := by
      intro i hi'
      rw [workspace_tablePoint tk.mem (by omega) (by omega), h.table i hi']
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, read_x, tc, point_counter_nonzero 0 (by decide), show decide ((0 : Nat) ≠ 0) = false from rfl], tv, td, h.keep.trans tk⟩
    · exact Or.inr ⟨by simp only [eval, read_x, tc, point_counter_nonzero k hk, decide_eq_true hk0],
        k, by omega, ⟨by omega, by omega, tk.scr h.scratch, tc,
          (tk.gpr _ (by decide) (by decide)).trans h.startReg, td, tv, hb', ht', h.keep.trans tk⟩⟩
  · exact ⟨by decide, by decide, hs, hc, hstart, hd, hp, hb, ht, CounterKeep.refl _ _⟩

theorem accumulateInit_ok (s : State) :
    WP isa (.block [.movz .w .x19 16 0]) s fun t => t.gpr .x19 = 16 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)


theorem accumulate16_ok {s : State} {base : Addr} (hs : Scr s base)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (hi : start + 16 ≤ 512)
    (hstart : s.gpr .x1 = BitVec.ofNat 64 start)
    (hb : ∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2))
    (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hp : point (env s.mem base) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, tablePoint s.mem base (5376 + 128 * i) = powerPoint p (start + i)) :
    WP isa accumulate16 s fun t => point (env t.mem base) 0 1 2 3 = after scalar p start ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ CounterKeep base s t := by
  rw [accumulate16]
  refine WP.seq (WP.mono (accumulateInit_ok s) fun a ⟨ac, ka⟩ => ?_)
  refine WP.mono (accumulateLoop_ok (hs.of_keeps ka (by decide)) start scalar p hi ac
    ((ka.gpr _ (by decide)).trans hstart) (by rw [ka.mem]; exact hb)
    (by rw [ka.mem]; exact hd) (by rw [ka.mem]; exact hp) (by rw [ka.mem]; exact ht))
    fun t ⟨tv, td, tk⟩ => ?_
  exact ⟨tv, td, (CounterKeep.of_keeps ka (by decide)).trans tk⟩

end VG.Proof.Ed25519.AArch64
