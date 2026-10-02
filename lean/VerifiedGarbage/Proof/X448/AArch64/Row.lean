import VerifiedGarbage.Proof.X448.AArch64.Step
import VerifiedGarbage.Proof.X448.Product
import VerifiedGarbage.Proof.Framework.Range

/-!
# X448 on AArch64: a row of multiplication

Sixteen multiply-adds update the coefficient array. Each coefficient is
visited once in a row, and the field operands are outside that array.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem rowBody_ok {s : State} {base : Addr} (hs : Scr s base) {b i a : Nat}
    (hb : b + 128 ≤ ACC) (hb8 : b % 8 = 0) (hi : i < 16) (ha : a < radix)
    (hc : (s.gpr .x6).toNat = a) (hr : s.gpr .x10 = off base (8 * i))
    {f g : Nat → Nat} (hf : ∀ k < 32, limbs s.mem base ACC k = f k)
    (hg : ∀ k < 16, limbs s.mem base b k = g k)
    (fb : ∀ k < 32, f k < 2 ^ 60) (gb : ∀ k < 16, g k < radix) :
    WP isa (.block ((List.range 16).flatMap (rowStep b))) s fun t =>
      (∀ k < 32, limbs t.mem base ACC k = addRow f a g i 16 k) ∧
      Outside base ACC 256 s.mem t.mem ∧ Keeps [.x4, .x5] s t := by
  let inv := fun n (t : State) =>
    (∀ k < 32, limbs t.mem base ACC k = addRow f a g i n k) ∧
    Outside base ACC 256 s.mem t.mem ∧ Keeps [.x4, .x5] s t
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block (rowStep b n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    have tc : (t.gpr .x6).toNat = a := by rw [tk.1 _ (by decide), hc]
    have tr : t.gpr .x10 = off base (8 * i) := (tk.1 _ (by decide)).trans hr
    have tg : limbs t.mem base b n = g n :=
      (tm.limbs (Or.inl hb) (Nat.le_trans hb (by decide)) hn).trans (hg n hn)
    have tv : limbs t.mem base ACC (i + n) = f (i + n) := by
      rw [tf (i + n) (by omega), addRow_at, ite_eq_right (by omega), Nat.add_zero]
    have hp : g n * a < 2 ^ 56 := by
      have hm := Nat.mul_le_mul (Nat.le_of_lt (gb n hn)) (Nat.le_of_lt ha)
      have hb' : g n * a ≤ (radix - 1) * (radix - 1) := Nat.mul_le_mul (by have := gb n hn; omega) (by omega)
      have hpow : (radix - 1) * (radix - 1) < 2 ^ 56 := by decide
      exact Nat.lt_of_le_of_lt hb' hpow
    have sum : (word t.mem base (b + 8 * n)).toNat * (t.gpr .x6).toNat +
        (word t.mem base (ACC + 8 * (i + n))).toNat < 2 ^ 64 := by
      change limbs t.mem base b n * (t.gpr .x6).toNat + limbs t.mem base ACC (i + n) < _
      rw [tg, tc, tv]
      have := fb (i + n) (by omega)
      omega
    refine WP.mono (rowStep_ok ts (by simp only [ACC] at hb; omega) hb8 hi hn tr sum)
      fun u ⟨um, uk⟩ => ?_
    have out : Outside base (ACC + 8 * (i + n)) 8 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [ACC]; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro k hk
    change (word u.mem base (ACC + 8 * k)).toNat = _
    rw [um, word_write t.mem base (by simp only [ACC]; omega) (by simp only [ACC]; omega)]
    by_cases he : k = i + n
    · rw [ite_eq_left he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sum]
      change limbs t.mem base b n * (t.gpr .x6).toNat + limbs t.mem base ACC (i + n) = _
      rw [tg, tc, ← he, tf k hk, addRow, addAt, ite_eq_left he, Nat.mul_comm (g n), Nat.add_comm]
    · rw [ite_eq_right he]
      change limbs t.mem base ACC k = _
      rw [tf k hk, addRow, addAt, ite_eq_right he]
  exact wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) s
    ⟨hf, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- Load the current row's multiplier through its public pointer. -/
theorem rowHead_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (ha : a + 128 ≤ ACC) (ha8 : a % 8 = 0) (hi : i < 16)
    (hr : s.gpr .x10 = off base (8 * i)) :
    WP isa (.block (rowHead a)) s fun t =>
      t.gpr .x6 = word s.mem base (a + 8 * i) ∧ t.mem = s.mem ∧ Keeps [.x6] s t := by
  have enc : a % 8 = 0 ∧ a < 32768 := ⟨ha8, by simp only [ACC] at ha; omega⟩
  have l := hs.read (d := a + 8 * i) (n := 8) (by simp only [ACC] at ha; omega)
  apply WP.of_runBlock
  simp only [rowHead, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    enc, and_self, hr, off, Offset.add_add, Nat.add_comm (8 * i), State.load, l,
    ite_true, Option.map_some, Option.bind_some, BitVec.setWidth_eq,
    read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  · simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- Advance the row index and form the loop condition. -/
theorem rowTail_ok {s : State} {base : Addr} {i : Nat} (hi : i < 16)
    (hc : s.gpr .x9 = BitVec.ofNat 64 i) (hr : s.gpr .x10 = off base (8 * i)) :
    WP isa (.block rowTail) s fun t =>
      t.gpr .x9 = BitVec.ofNat 64 (i + 1) ∧ t.gpr .x10 = off base (8 * (i + 1)) ∧
      (t.gpr .x11 == 0) = decide (i + 1 = 16) ∧ t.mem = s.mem ∧ Keeps [.x9, .x10, .x11] s t := by
  have eq : ((BitVec.ofNat 64 i + BitVec.ofNat 64 1 - BitVec.ofNat 64 16) == 0) = decide (i + 1 = 16) := by
    have check : ∀ n < 16,
        ((BitVec.ofNat 64 n + BitVec.ofNat 64 1 - BitVec.ofNat 64 16) == 0) = decide (n + 1 = 16) :=
      by decide +kernel
    exact check i hi
  apply WP.of_runBlock
  simp only [rowTail, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceLT, RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false,
    reduceCtorEq, hc, hr, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, eq, rfl, (fun r hr => ?_), rfl, rfl⟩
  · exact (BitVec.ofNat_add _ _).symm
  · rw [off, Offset.add_add]; congr 2
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- One loop iteration, including the public row counter. -/
theorem row_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : a + 128 ≤ ACC) (ha8 : a % 8 = 0) (hb : b + 128 ≤ ACC) (hb8 : b % 8 = 0) (hi : i < 16)
    (hc : s.gpr .x9 = BitVec.ofNat 64 i) (hr : s.gpr .x10 = off base (8 * i))
    {f g : Nat → Nat} (hf : ∀ k < 32, limbs s.mem base ACC k = f k)
    (hg : ∀ k < 16, limbs s.mem base b k = g k)
    (fb : ∀ k < 32, f k < 2 ^ 60) (gb : ∀ k < 16, g k < radix)
    (ab : limbs s.mem base a i < radix) :
    WP isa (.block (row a b)) s fun t =>
      (∀ k < 32, limbs t.mem base ACC k = addRow f (limbs s.mem base a i) g i 16 k) ∧
      t.gpr .x9 = BitVec.ofNat 64 (i + 1) ∧ t.gpr .x10 = off base (8 * (i + 1)) ∧
      (t.gpr .x11 == 0) = decide (i + 1 = 16) ∧ Outside base ACC 256 s.mem t.mem ∧
      Keeps [.x4, .x6, .x5, .x9, .x10, .x11] s t := by
  rw [row, List.append_assoc, WP.block_append_iff]
  refine WP.mono (rowHead_ok hs ha ha8 hi hr) fun t ⟨tc, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rowBody_ok (hs.of_keeps tk (by decide)) hb hb8 hi ab
    (by rw [tc]) ((tk.1 _ (by decide)).trans hr)
    (by intro k hk; rw [tm]; exact hf k hk)
    (by intro k hk; rw [tm]; exact hg k hk) fb gb) fun u ⟨uf, um, uk⟩ => ?_
  have uc : u.gpr .x9 = BitVec.ofNat 64 i :=
    (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hc)
  have ur : u.gpr .x10 = off base (8 * i) :=
    (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hr)
  refine WP.mono (rowTail_ok hi uc ur) fun v ⟨vc, vr, vz, vm, vk⟩ => ?_
  refine ⟨?_, vc, vr, vz, ?_, ?_⟩
  · intro k hk; rw [vm]; exact uf k hk
  · rw [vm, ← tm]; exact um
  · have k₁ : Keeps [.x4, .x6, .x5, .x9, .x10, .x11] s t := tk.mono (by
      intro r h
      simp only [List.mem_singleton] at h
      subst r
      decide)
    have k₂ : Keeps [.x4, .x6, .x5, .x9, .x10, .x11] t u := uk.mono (by
      intro r h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> decide)
    have k₃ : Keeps [.x4, .x6, .x5, .x9, .x10, .x11] u v := vk.mono (by
      intro r h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> decide)
    exact k₁.trans (k₂.trans k₃)

end VG.Proof.X448.AArch64
