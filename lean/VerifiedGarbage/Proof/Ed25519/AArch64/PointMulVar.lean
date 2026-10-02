import VerifiedGarbage.Impl.Ed25519.AArch64.PointMulVar
import VerifiedGarbage.Proof.Ed25519.AArch64.BaseAccumulate

/-!
# Variable-time bit loops: correctness

Untrusted. The loop over a batch's sixteen bits for any addition `add` that
adds `q` to the accumulator when slots 4–7 hold `f q` (`AddSpec`): exact
powers with `pointAdd` (`f = id`), cached ones with `pointAddCached`
(`f = cache`). A clear bit leaves the accumulator alone, which is the
specification's step too (`after_step`).
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

/-- `add` adds `q` to the accumulator in slots 0–3 when slots 4–7 hold `f q`. -/
def AddSpec (add : List Instr) (f : Spec.Ed25519.Point → Spec.Ed25519.Point) : Prop :=
  ∀ (s : State) (base : Addr) (q : Spec.Ed25519.Point), Scr s base →
    env s.mem base 16 = Spec.Ed25519.d → point (env s.mem base) 4 5 6 7 = f q →
    WP isa (.block add) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i

theorem pointAdd_spec : AddSpec pointAdd id := fun _ _ _ hs hd hq =>
  WP.mono (pointAdd_ok hs hd) fun _ ⟨k, v, h⟩ => ⟨k, v.trans (by rw [hq]; rfl), h⟩

theorem pointAddCached_spec : AddSpec pointAddCached cache := fun _ _ q hs _ hq =>
  pointAddCached_ok hs q hq

theorem addEntry_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s : State} {base : Addr} (hs : Scr s base)
    (j : Nat) (hj : j < 16) (hc : s.gpr .x19 = BitVec.ofNat 64 j) (q : Spec.Ed25519.Point)
    (hq : tablePoint s.mem base (5376 + 128 * j) = f q) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (addEntry add)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      env t.mem base 16 = env s.mem base 16 := by
  rw [addEntry, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableAddr_ok hs.x0 5376 j (by omega) hc) fun a ⟨pa, ka⟩ => ?_
  have kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (kae.scr hs) pa (by omega) (by omega)) fun b ⟨pb, kb⟩ => ?_
  have kbe := Keep.of_tableQ kb
  have o := tableQ_other kb
  have bp : point (env b.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, o 0 (by decide), o 1 (by decide), o 2 (by decide), o 3 (by decide), ka.mem]
  have bq : point (env b.mem base) 4 5 6 7 = f q := by rw [pb, ka.mem, hq]
  have bd : env b.mem base 16 = env s.mem base 16 := by rw [o 16 (by decide), ka.mem]
  refine WP.mono (hadd b base q ((kae.trans kbe).scr hs) (bd.trans hd) bq) fun t ⟨kt, tp, th⟩ => ?_
  exact ⟨(kae.trans kbe).trans kt, by rw [tp, bp], by rw [th 16 (by decide), bd]⟩

theorem scalarBitLoad_ok {s : State} {base : Addr} (hs : Scr s base)
    (j start bit : Nat) (hi : start + j < 512) (hbit : bit < 2)
    (hj : s.gpr .x19 = BitVec.ofNat 64 j) (hstart : s.gpr .x1 = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + j))) = BitVec.ofNat 8 bit) :
    WP isa (.block scalarBitLoad) s fun t =>
      eval (.nonzero .x .x3) t = some (decide (bit ≠ 0)) ∧ Keeps [.x8, .x3] s t := by
  have _hcap : workSize true = 8192 := rfl
  have hr : InRegions (s.rd ++ s.wr) (off base (768 + (start + j))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : base + (BitVec.ofNat 64 j + BitVec.ofNat 64 start) + BitVec.ofNat 64 768 =
      off base (768 + (start + j)) := by
    rw [← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (off base) (by omega)
  have hm : (((BitVec.ofNat 8 bit).setWidth 32).setWidth 64 != 0) = decide (bit ≠ 0) := by
    have h : bit = 0 ∨ bit = 1 := by omega
    rcases h with rfl | rfl <;> decide
  apply WP.of_runBlock
  simp only [scalarBitLoad, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.load, addr, Size.bits, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT,
    and_self, hj, hstart, hs.x0, he, hr, read_byte, hb,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [eval, read_x, RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, hm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem accumulateVarBody_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s : State} {base : Addr} (hs : Scr s base)
    (n start scalar : Nat) (p : Spec.Ed25519.Point) (hn : n < 16) (hi : start + n < 512)
    (hc : s.gpr .x19 = BitVec.ofNat 64 (n + 1)) (hstart : s.gpr .x1 = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + n))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + n)) % 2))
    (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hp : point (env s.mem base) 0 1 2 3 = after scalar p (start + n + 1))
    (ht : tablePoint s.mem base (5376 + 128 * n) = f (powerPoint p (start + n))) :
    WP isa (accumulateVarBody add) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 n ∧
      point (env t.mem base) 0 1 2 3 = after scalar p (start + n) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ CounterKeep base s t := by
  rw [accumulateVarBody]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (accumulateDec_ok s n hc) fun a ⟨ac, ka⟩ => ?_
  have ha := hs.of_keeps ka (by decide)
  refine WP.mono (scalarBitLoad_ok ha n start ((scalar / 2 ^ (start + n)) % 2) hi (by omega) ac
    ((ka.gpr _ (by decide)).trans hstart) (by rw [ka.mem]; exact hb)) fun b ⟨bz, kb⟩ => ?_
  have kab : Keeps [.x19, .x8, .x3] s b := (ka.mono (by decide)).trans (kb.mono (by decide))
  have hbs := hs.of_keeps kab (by decide)
  have bc : b.gpr .x19 = BitVec.ofNat 64 n := (kb.gpr _ (by decide)).trans ac
  refine WP.ite (decide ((scalar / 2 ^ (start + n)) % 2 ≠ 0)) bz (fun h => ?_) (fun h => ?_)
  · have h1 : (scalar / 2 ^ (start + n)) % 2 ≠ 0 := of_decide_eq_true h
    refine WP.mono (addEntry_ok hadd hbs n hn bc (powerPoint p (start + n)) (by rw [kab.mem]; exact ht)
      (by rw [kab.mem]; exact hd)) fun t ⟨kt, tp, td⟩ => ?_
    refine ⟨(kt.gpr _ (by decide)).trans bc, ?_, by rw [td, kab.mem]; exact hd,
      (CounterKeep.of_keeps kab (by decide)).trans (CounterKeep.of_keep kt)⟩
    rw [tp, kab.mem, hp, after_step scalar p (start + n)]
    simp only [h1, ↓reduceIte]
  · have h0 : (scalar / 2 ^ (start + n)) % 2 = 0 := Decidable.of_not_not (of_decide_eq_false h)
    refine WP.block_nil ⟨bc, ?_, by rw [kab.mem]; exact hd, CounterKeep.of_keeps kab (by decide)⟩
    rw [kab.mem, hp, after_step scalar p (start + n)]
    simp only [h0, ↓reduceIte]

structure AccumulateVarInv (f : Spec.Ed25519.Point → Spec.Ed25519.Point) (s₀ : State) (base : Addr)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  scratch : Scr s base
  counter : s.gpr .x19 = BitVec.ofNat 64 n
  startReg : s.gpr .x1 = BitVec.ofNat 64 start
  d : env s.mem base 16 = Spec.Ed25519.d
  value : point (env s.mem base) 0 1 2 3 = after scalar p (start + n)
  bits : ∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2)
  table : ∀ i < 16, tablePoint s.mem base (5376 + 128 * i) = f (powerPoint p (start + i))
  keep : CounterKeep base s₀ s

theorem accumulateVarStep_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s₀ s : State} {base : Addr} {start scalar : Nat} {p : Spec.Ed25519.Point}
    {k : Nat} (hi : start + 16 ≤ 512) (h : AccumulateVarInv f s₀ base start scalar p (k + 1) s) :
    WP isa (accumulateVarBody add) s fun t => t.gpr .x19 = BitVec.ofNat 64 k ∧
      point (env t.mem base) 0 1 2 3 = after scalar p (start + k) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ CounterKeep base s₀ t ∧
      (k ≠ 0 → AccumulateVarInv f s₀ base start scalar p k t) := by
  have hk : k < 16 := by have := h.bound; omega
  refine WP.mono (accumulateVarBody_ok hadd h.scratch k start scalar p hk (by omega) h.counter
    h.startReg (h.bits k hk) h.d (by rw [Nat.add_assoc]; exact h.value) (h.table k hk))
    fun t ⟨tc, tv, td, tk⟩ => ?_
  refine ⟨tc, tv, td, h.keep.trans tk, fun hk0 => ⟨by omega, by omega, tk.scr h.scratch, tc,
    (tk.gpr _ (by decide) (by decide)).trans h.startReg, td, tv, ?_, ?_, h.keep.trans tk⟩⟩
  · intro i hi'
    rw [tk.mem _ (by rw [ofs_off' base (by omega)]; omega), h.bits i hi']
  · intro i hi'
    rw [workspace_tablePoint tk.mem (by omega) (by omega), h.table i hi']

theorem accumulateVarLoop_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s₀ s₁ : State} {base : Addr} (start scalar : Nat) (p : Spec.Ed25519.Point)
    (hi : start + 16 ≤ 512) (h₀ : AccumulateVarInv f s₀ base start scalar p 16 s₁) :
    WP isa (.loop (accumulateVarBody add) (.nonzero .x .x19)) s₁ fun t =>
      point (env t.mem base) 0 1 2 3 = after scalar p start ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ CounterKeep base s₀ t := by
  apply WP.loop (AccumulateVarInv f s₀ base start scalar p) (n := 16)
  · intro n s h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := h.bound; omega
    refine WP.mono (accumulateVarStep_ok hadd hi h) fun t ⟨tc, tv, td, tk, tn⟩ => ?_
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, read_x, tc, point_counter_nonzero 0 (by decide),
        show decide ((0 : Nat) ≠ 0) = false from rfl], tv, td, tk⟩
    · exact Or.inr ⟨by simp only [eval, read_x, tc, point_counter_nonzero k hk, decide_eq_true hk0],
        k, by omega, tn hk0⟩
  · exact h₀

/-- Before a batch's bits: what `accumulateVar16` needs. -/
def AccumulateVarPre (f : Spec.Ed25519.Point → Spec.Ed25519.Point) (base : Addr) (start scalar : Nat)
    (p : Spec.Ed25519.Point) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x1 = BitVec.ofNat 64 start ∧
    (∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2)) ∧
    env s.mem base 16 = Spec.Ed25519.d ∧
    point (env s.mem base) 0 1 2 3 = after scalar p (start + 16) ∧
    (∀ i < 16, tablePoint s.mem base (5376 + 128 * i) = f (powerPoint p (start + i)))

theorem AccumulateVarPre.init {f : Spec.Ed25519.Point → Spec.Ed25519.Point} {base : Addr}
    {start scalar : Nat} {p : Spec.Ed25519.Point} {s t : State}
    (h : AccumulateVarPre f base start scalar p s) (tc : t.gpr .x19 = 16) (tk : Keeps [.x19] s t) :
    AccumulateVarInv f s base start scalar p 16 t :=
  ⟨by decide, by decide, h.1.of_keeps tk (by decide), tc, (tk.gpr _ (by decide)).trans h.2.1,
    by rw [tk.mem]; exact h.2.2.2.1, by rw [tk.mem]; exact h.2.2.2.2.1, by rw [tk.mem]; exact h.2.2.1,
    by rw [tk.mem]; exact h.2.2.2.2.2, CounterKeep.of_keeps tk (by decide)⟩

theorem accumulateVar16_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s : State} {base : Addr} {start scalar : Nat} {p : Spec.Ed25519.Point}
    (hi : start + 16 ≤ 512) (h : AccumulateVarPre f base start scalar p s) :
    WP isa (accumulateVar16 add) s fun t => point (env t.mem base) 0 1 2 3 = after scalar p start ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ CounterKeep base s t := by
  rw [accumulateVar16]
  refine WP.seq (WP.mono (accumulateInit_ok s) fun a ⟨ac, ka⟩ => ?_)
  exact accumulateVarLoop_ok hadd start scalar p hi (h.init ac ka)

end VG.Proof.Ed25519.AArch64
