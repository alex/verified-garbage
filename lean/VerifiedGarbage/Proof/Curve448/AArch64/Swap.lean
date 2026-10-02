import VerifiedGarbage.Proof.Curve448.AArch64.Copy

/-!
# X448 on AArch64: constant-time conditional swaps

Untrusted: everything here is checked by Lean. An XOR mask exchanges the
limbs without a branch or an address depending on the swap bit.
-/

namespace VG.Proof.Curve448.AArch64

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.AArch64
open VG.Impl.Curve448.AArch64

def mask (sw : Bool) : BitVec 64 := if sw then BitVec.allOnes 64 else 0

theorem xor_sel (sw : Bool) (a b : BitVec 64) :
    a ^^^ ((a ^^^ b) &&& mask sw) = (if sw then b else a) ∧
      b ^^^ ((a ^^^ b) &&& mask sw) = (if sw then a else b) := by
  cases sw
  · simp only [mask, Bool.false_eq_true, ite_false]
    constructor <;> (apply BitVec.eq_of_toNat_eq; simp)
  · simp only [mask, ite_true, BitVec.and_allOnes]
    constructor
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem swapStep_ok {s : State} {base : Addr} (hs : Scr s base) {x y i : Nat}
    (hx : Slot x) (hy : Slot y) (hx8 : x % 8 = 0) (hy8 : y % 8 = 0) (hi : i < 8) {sw : Bool} (hc : s.gpr .x6 = mask sw) :
    WP isa (.block
      [ld .x4 (x + 8 * i), ld .x5 (y + 8 * i), .logic .eor .x .x7 .x4 .x5,
        .logic .and .x .x7 .x7 .x6, .logic .eor .x .x4 .x4 .x7,
        .logic .eor .x .x5 .x5 .x7, st .x4 (x + 8 * i), st .x5 (y + 8 * i)]) s fun t =>
      t.mem = (s.mem.writeW (off base (x + 8 * i))
        (if sw then word s.mem base (y + 8 * i) else word s.mem base (x + 8 * i))).writeW
        (off base (y + 8 * i)) (if sw then word s.mem base (x + 8 * i) else word s.mem base (y + 8 * i)) ∧
      Keeps [.x4, .x5, .x7] s t := by
  have lx := hs.read (d := x + 8 * i) (n := 8) (by change x + 128 ≤ 3584 at hx; omega)
  have ly := hs.read (d := y + 8 * i) (n := 8) (by change y + 128 ≤ 3584 at hy; omega)
  have wx := hs.write (d := x + 8 * i) (n := 8) (by change x + 128 ≤ 3584 at hx; omega)
  have wy := hs.write (d := y + 8 * i) (n := 8) (by change y + 128 ≤ 3584 at hy; omega)
  have xe : (x + 8 * i) % 8 = 0 ∧ x + 8 * i < 32768 := by
    change x + 128 ≤ 3584 at hx; omega
  have ye : (y + 8 * i) % 8 = 0 ∧ y + 8 * i < 32768 := by
    change y + 128 ≤ 3584 at hy; omega
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, xe, ye, and_self,
    hs.x3, hc, lx, ly, wx, wy, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, read8_eq, write8_eq, Option.some.injEq, exists_eq_left']
  simp only [(xor_sel sw _ _).1, (xor_sel sw _ _).2]
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- Reading two disjoint words after writing a limb pair. -/
theorem pair_write {m : Mem} {base : Addr} {x y n j : Nat} (hx : Slot x) (hy : Slot y)
    (hxy : x + 128 ≤ y ∨ y + 128 ≤ x) (hn : n < 8) (hj : j < 8) (vx vy : BitVec 64) :
    let m' := (m.writeW (off base (x + 8 * n)) vx).writeW (off base (y + 8 * n)) vy
    limbs m' base x j = (if j = n then vx.toNat else limbs m base x j) ∧
    limbs m' base y j = (if j = n then vy.toNat else limbs m base y j) := by
  have xb : x + 128 ≤ 8192 := Nat.le_trans hx (by decide)
  have yb : y + 128 ≤ 8192 := Nat.le_trans hy (by decide)
  dsimp only
  constructor
  · simp only [limbs, word]
    rw [Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)]
    rw [show m.readW (off base (x + 8 * j)) 64 = word m base (x + 8 * j) from rfl]
    change (word (m.writeW (off base (x + 8 * n)) vx) base (x + 8 * j)).toNat = _
    rw [word_write m base (by omega) (by omega)]
    split <;> rfl
  · change (word ((m.writeW (off base (x + 8 * n)) vx).writeW (off base (y + 8 * n)) vy)
      base (y + 8 * j)).toNat = _
    rw [word_write (m.writeW (off base (x + 8 * n)) vx) base (by omega) (by omega)]
    by_cases h : j = n
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      apply congrArg BitVec.toNat
      exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

/-- Swap all eight limbs under the mask, preserving all other bytes. -/
theorem cswap_ok {s : State} {base : Addr} (hs : Scr s base) {x y : Nat} (hx : Slot x) (hy : Slot y)
    (hx8 : x % 8 = 0) (hy8 : y % 8 = 0)
    (hxy : x + 128 ≤ y ∨ y + 128 ≤ x) {sw : Bool} (hc : s.gpr .x6 = mask sw) :
    WP isa (.block (cswap x y)) s fun t =>
      (∀ i < 8, limbs t.mem base x i = if sw then limbs s.mem base y i else limbs s.mem base x i) ∧
      (∀ i < 8, limbs t.mem base y i = if sw then limbs s.mem base x i else limbs s.mem base y i) ∧
      Outside2 base x 128 y 128 s.mem t.mem ∧ Keeps [.x4, .x5, .x7] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base x i = if sw then limbs s.mem base y i else limbs s.mem base x i) ∧
    (∀ i < n, limbs t.mem base y i = if sw then limbs s.mem base x i else limbs s.mem base y i) ∧
    Outside2 base x (8 * n) y (8 * n) s.mem t.mem ∧ Keeps [.x4, .x5, .x7] s t
  have xb : x + 128 ≤ 8192 := Nat.le_trans hx (by decide)
  have yb : y + 128 ≤ 8192 := Nat.le_trans hy (by decide)
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block
      [ld .x4 (x + 8 * n), ld .x5 (y + 8 * n), .logic .eor .x .x7 .x4 .x5,
        .logic .and .x .x7 .x7 .x6, .logic .eor .x .x4 .x4 .x7,
        .logic .eor .x .x5 .x5 .x7, st .x4 (x + 8 * n), st .x5 (y + 8 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tc := (tk.1 .x6 (by decide)).trans hc
    refine WP.mono (swapStep_ok (hs.of_keeps tk (by decide)) hx hy hx8 hy8 hn tc) fun u ⟨um, uk⟩ => ?_
    have ex : limbs t.mem base x n = limbs s.mem base x n :=
      congrArg BitVec.toNat (tm.word (by omega) (by omega) (by omega))
    have ey : limbs t.mem base y n = limbs s.mem base y n :=
      congrArg BitVec.toNat (tm.word (by omega) (by omega) (by omega))
    have pair := fun (j : Nat) (hj : j < 8) => pair_write (m := t.mem) (base := base) hx hy hxy hn hj
      (if sw then word t.mem base (y + 8 * n) else word t.mem base (x + 8 * n))
      (if sw then word t.mem base (x + 8 * n) else word t.mem base (y + 8 * n))
    refine ⟨?_, ?_, ?_, tk.trans uk⟩
    · intro j hj
      rw [um, (pair j (by omega)).1]
      by_cases h : j = n
      · rw [ite_eq_left h, h]
        cases sw <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> with_reducible assumption
      · rw [ite_eq_right h]; exact tx j (by omega)
    · intro j hj
      rw [um, (pair j (by omega)).2]
      by_cases h : j = n
      · rw [ite_eq_left h, h]
        cases sw <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> with_reducible assumption
      · rw [ite_eq_right h]; exact ty j (by omega)
    · refine (tm.mono (by omega) (by omega)).trans ?_
      intro p hp hq
      rw [um, writeW_outside _ _ _ (by omega : y + 8 * n + 8 ≤ 8192) p (by omega),
        writeW_outside _ _ _ (by omega : x + 8 * n + 8 ≤ 8192) p (by omega)]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, fun _ hi => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tx, ty, tm, tk⟩ => ?_
  exact ⟨tx, ty, tm.mono (by decide) (by decide), tk⟩

end VG.Proof.Curve448.AArch64
