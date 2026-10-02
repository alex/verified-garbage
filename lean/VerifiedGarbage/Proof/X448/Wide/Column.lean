import VerifiedGarbage.Proof.X448.Wide.Memory
import VerifiedGarbage.Proof.Framework.Range

/-! Untrusted: a diagonal of an eight-by-eight product, accumulated in registers. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Impl.X448.AArch64.Wide VG.Proof.X448.AArch64

/-- Load one pair of operands without changing the coefficient registers. -/
theorem loadTerm_ok {s : State} {base : Addr} (hs : Scr s base) {a b i j : Nat}
    (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hi : i < 8) (hj : j < 8) :
    WP isa (.block [ld .x6 (a + 8 * i), ld .x9 (b + 8 * j)]) s fun t =>
      t.gpr .x6 = word s.mem base (a + 8 * i) ∧
      t.gpr .x9 = word s.mem base (b + 8 * j) ∧
      t.mem = s.mem ∧ Keeps [.x6, .x9] s t := by
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := ⟨by omega, by omega⟩
  have be : (b + 8 * j) % 8 = 0 ∧ b + 8 * j < 32768 := ⟨by omega, by omega⟩
  have al := hs.read (d := a + 8 * i) (n := 8) (by omega)
  have bl := hs.read (d := b + 8 * j) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, be, and_self, State.load, hs.x3, al, bl, ite_true, Option.map_some,
    Option.bind_some, BitVec.setWidth_eq, read8_eq, RegUpd.gpr_write,
    ite_false, reduceCtorEq, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- Initialize a register coefficient to zero. -/
theorem zero_ok (s : State) :
    WP isa (.block [.movz .x .x4 0 0, .movz .x .x5 0 0]) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = 0 ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits from by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, ite_false,
    reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- Write the two coefficient words. -/
theorem store_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 16) :
    WP isa (.block [st .x4 (ACC + 16 * k), st .x5 (ACC + 16 * k + 8)]) s fun t =>
      t.mem = putCoeff s.mem base ACC k (s.gpr .x4) (s.gpr .x5) ∧ Keeps [] s t := by
  have ae : (ACC + 16 * k) % 8 = 0 ∧ ACC + 16 * k < 32768 := by simp only [ACC]; omega
  have be : (ACC + 16 * k + 8) % 8 = 0 ∧ ACC + 16 * k + 8 < 32768 := by simp only [ACC]; omega
  have aw := hs.write (d := ACC + 16 * k) (n := 8) (by simp only [ACC]; omega)
  have bw := hs.write (d := ACC + 16 * k + 8) (n := 8) (by simp only [ACC]; omega)
  apply WP.of_runBlock
  simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    ae, be, and_self, State.read, State.store, hs.x3, aw, bw, ite_true,
    Option.bind_some, BitVec.setWidth_eq, write8_eq,
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, (fun _ _ => rfl), rfl, rfl⟩

def colRegs : List Reg := [.x4, .x5, .x6, .x9, .x10, .x11]

theorem columnBody_ok {s : State} {base : Addr} (hs : Scr s base) {a b k : Nat}
    (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (fa : ∀ i < 8, limbs s.mem base a i < radix)
    (fb : ∀ i < 8, limbs s.mem base b i < radix)
    (hz : pair (s.gpr .x4) (s.gpr .x5) = 0) :
    WP isa (.block ((List.range 8).flatMap (fun i => if i ≤ k ∧ k < i + 8 then
      [ld .x6 (a + 8 * i), ld .x9 (b + 8 * (k - i))] ++ term else []))) s fun t =>
      pair (t.gpr .x4) (t.gpr .x5) = rows (limbs s.mem base a) (limbs s.mem base b) 8 k ∧
      t.mem = s.mem ∧ Keeps colRegs s t := by
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  let inv := fun n (t : State) =>
    pair (t.gpr .x4) (t.gpr .x5) = colSum f g k n ∧
    t.mem = s.mem ∧ Keeps colRegs s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block (if n ≤ k ∧ k < n + 8 then
        [ld .x6 (a + 8 * n), ld .x9 (b + 8 * (k - n))] ++ term else [])) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    by_cases h : n ≤ k ∧ k < n + 8
    · rw [ite_eq_left h, WP.block_append_iff]
      have ts := hs.of_keeps tk (by decide)
      refine WP.mono (loadTerm_ok ts ha hb ha8 hb8 hn (by omega)) fun u ⟨u6, u9, um, uk⟩ => ?_
      have uv : pair (u.gpr .x4) (u.gpr .x5) = colSum f g k n := by
        rw [uk.1 .x4 (by decide), uk.1 .x5 (by decide), tv]
      have av : (u.gpr .x6).toNat = f n := by rw [u6, tm]
      have bv : (u.gpr .x9).toNat = g (k - n) := by rw [u9, tm]
      have prod : f n * g (k - n) ≤ (radix - 1) ^ 2 := by
        rw [Nat.pow_two]
        exact Nat.mul_le_mul (by have fh : f n < radix := fa n hn; omega) (by have gh : g (k - n) < radix := fb (k - n) (by omega); omega)
      have cb := rows_bound fa fb (n := n) (by omega) k
      rw [← colSum_eq] at cb
      change colSum f g k n ≤ n * (radix - 1) ^ 2 at cb
      have sum : (u.gpr .x6).toNat * (u.gpr .x9).toNat + pair (u.gpr .x4) (u.gpr .x5) < 2 ^ 128 := by
        rw [av, bv, uv]
        have bd : (n + 1) * (radix - 1) ^ 2 ≤ 8 * (radix - 1) ^ 2 :=
          Nat.mul_le_mul_right _ (by omega)
        have cap : 8 * (radix - 1) ^ 2 < 2 ^ 128 := by decide +kernel
        rw [Nat.add_mul, Nat.one_mul] at bd
        omega
      refine WP.mono (term_ok u sum) fun v ⟨vv, vm, vk⟩ => ?_
      refine ⟨?_, vm.trans (um.trans tm), ?_⟩
      · rw [vv, av, bv, uv, colSum, ite_eq_left h]
        omega
      · exact tk.trans ((uk.mono (by decide)).trans (vk.mono (by decide)))
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by rw [colSum, ite_eq_right h, Nat.add_zero]; exact tv, tm, tk⟩
  have init : inv 0 s := ⟨hz, rfl, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s init)
    fun t ⟨tv, tm, tk⟩ => ?_
  exact ⟨tv.trans (colSum_eq f g k 8), tm, tk⟩

theorem column_ok {s : State} {base : Addr} (hs : Scr s base) {a b k : Nat}
    (ha : a + 64 ≤ 8192) (hb : b + 64 ≤ 8192)
    (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) (hk : k < 16)
    (fa : ∀ i < 8, limbs s.mem base a i < radix)
    (fb : ∀ i < 8, limbs s.mem base b i < radix) :
    WP isa (.block (column a b k)) s fun t =>
      coeff t.mem base ACC k = rows (limbs s.mem base a) (limbs s.mem base b) 8 k ∧
      Outside base (ACC + 16 * k) 16 s.mem t.mem ∧ Keeps colRegs s t := by
  rw [column, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun u ⟨uz, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (columnBody_ok (hs.of_keeps uk (by decide)) ha hb ha8 hb8
    (by rw [um]; exact fa) (by rw [um]; exact fb) uz) fun v ⟨vv, vm, vk⟩ => ?_
  have vs := (hs.of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (store_ok vs hk) fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [tm, coeff_put _ base _ _ (by simp only [ACC]; omega)
      (by simp only [ACC]; omega), ite_eq_left rfl, vv, um]
  · rw [tm, vm, um]
    exact putCoeff_outside _ _ _ _ (by simp only [ACC]; omega)
  · exact (uk.mono (by decide)).trans (vk.trans (tk.mono (by decide)))

end VG.Proof.X448.Wide
