import VerifiedGarbage.Proof.X448.X86.Copy
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# X448 on x86 (32-bit): constant-time conditional swaps

Untrusted: everything here is checked by Lean. An XOR mask swaps limbs
without a secret-dependent branch or memory address.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

def mask (sw : Bool) : BitVec 32 := if sw then BitVec.allOnes 32 else 0

theorem xor_sel (sw : Bool) (a b : BitVec 32) :
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
    (hx : Slot x) (hy : Slot y) (hi : i < 28) {sw : Bool} (hc : s.gpr .ebx = mask sw) :
    WP isa (.block
      [ld .eax (x + 4 * i), ld .ecx (y + 4 * i), .mov .edx (.reg .eax), .alu .xor .edx (.reg .ecx),
        .alu .and .edx (.reg .ebx), .alu .xor .eax (.reg .edx),
        .alu .xor .ecx (.reg .edx), st .eax (x + 4 * i), st .ecx (y + 4 * i)]) s fun t =>
      t.mem = (s.mem.writeW (off base (x + 4 * i))
        (if sw then word s.mem base (y + 4 * i) else word s.mem base (x + 4 * i))).writeW
        (off base (y + 4 * i)) (if sw then word s.mem base (x + 4 * i) else word s.mem base (y + 4 * i)) ∧
      Keeps [.eax, .ecx, .edx] s t := by
  have hx' : x + 112 ≤ 3584 := hx
  have hy' : y + 112 ≤ 3584 := hy
  have lx := hs.read (d := x + 4 * i) (n := 4) (by omega)
  have ly := hs.read (d := y + 4 * i) (n := 4) (by omega)
  have wx := hs.write (d := x + 4 * i) (n := 4) (by omega)
  have wy := hs.write (d := y + 4 * i) (n := 4) (by omega)
  have xe := hs.ea (d := x + 4 * i) (by omega)
  have ye := hs.ea (d := y + 4 * i) (by omega)
  simp only [State.ea, sc, at_] at xe ye
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, sc, at_,
    State.load32, State.store32, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, xe, ye, hc, lx, ly, wx, wy,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  simp only [(xor_sel sw _ _).1, (xor_sel sw _ _).2]
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]

/-- Reading two disjoint words after writing a limb pair. -/
theorem pair_write {m : Mem} {base : Addr} {x y n j : Nat} (hx : Slot x) (hy : Slot y)
    (hxy : x + 112 ≤ y ∨ y + 112 ≤ x) (hn : n < 28) (hj : j < 28) (vx vy : BitVec 32) :
    let m' := (m.writeW (off base (x + 4 * n)) vx).writeW (off base (y + 4 * n)) vy
    limbs m' base x j = (if j = n then vx.toNat else limbs m base x j) ∧
    limbs m' base y j = (if j = n then vy.toNat else limbs m base y j) := by
  have xb : x + 112 ≤ 8192 := Nat.le_trans hx (by decide)
  have yb : y + 112 ≤ 8192 := Nat.le_trans hy (by decide)
  dsimp only
  constructor
  · simp only [limbs, word]
    rw [Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)]
    rw [show m.readW (off base (x + 4 * j)) 32 = word m base (x + 4 * j) from rfl]
    change (word (m.writeW (off base (x + 4 * n)) vx) base (x + 4 * j)).toNat = _
    rw [word_write m base (by omega) (by omega)]
    split <;> rfl
  · change (word ((m.writeW (off base (x + 4 * n)) vx).writeW (off base (y + 4 * n)) vy)
      base (y + 4 * j)).toNat = _
    rw [word_write (m.writeW (off base (x + 4 * n)) vx) base (by omega) (by omega)]
    by_cases h : j = n
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      apply congrArg BitVec.toNat
      exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

/-- Swap all twenty-eight limbs under the mask, preserving all other bytes. -/
theorem cswap_ok {s : State} {base : Addr} (hs : Scr s base) {x y : Nat} (hx : Slot x) (hy : Slot y)
    (hxy : x + 112 ≤ y ∨ y + 112 ≤ x) {sw : Bool} (hc : s.gpr .ebx = mask sw) :
    WP isa (.block (cswap x y)) s fun t =>
      (∀ i < 28, limbs t.mem base x i = if sw then limbs s.mem base y i else limbs s.mem base x i) ∧
      (∀ i < 28, limbs t.mem base y i = if sw then limbs s.mem base x i else limbs s.mem base y i) ∧
      Outside2 base x 112 y 112 s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base x i = if sw then limbs s.mem base y i else limbs s.mem base x i) ∧
    (∀ i < n, limbs t.mem base y i = if sw then limbs s.mem base x i else limbs s.mem base y i) ∧
    Outside2 base x (4 * n) y (4 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t
  have xb : x + 112 ≤ 8192 := Nat.le_trans hx (by decide)
  have yb : y + 112 ≤ 8192 := Nat.le_trans hy (by decide)
  have step : ∀ n t, n < 28 → inv n t → WP isa (.block
      [ld .eax (x + 4 * n), ld .ecx (y + 4 * n), .mov .edx (.reg .eax), .alu .xor .edx (.reg .ecx),
        .alu .and .edx (.reg .ebx), .alu .xor .eax (.reg .edx),
        .alu .xor .ecx (.reg .edx), st .eax (x + 4 * n), st .ecx (y + 4 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tc := (tk.1 .ebx (by decide)).trans hc
    refine WP.mono (swapStep_ok (hs.of_keeps tk (by decide)) hx hy hn tc) fun u ⟨um, uk⟩ => ?_
    have ex : limbs t.mem base x n = limbs s.mem base x n :=
      congrArg BitVec.toNat (tm.word (by omega) (by omega) (by omega))
    have ey : limbs t.mem base y n = limbs s.mem base y n :=
      congrArg BitVec.toNat (tm.word (by omega) (by omega) (by omega))
    have pair := fun (j : Nat) (hj : j < 28) => pair_write (m := t.mem) (base := base) hx hy hxy hn hj
      (if sw then word t.mem base (y + 4 * n) else word t.mem base (x + 4 * n))
      (if sw then word t.mem base (x + 4 * n) else word t.mem base (y + 4 * n))
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
      rw [um, writeW_outside _ _ _ (by omega : y + 4 * n + 4 ≤ 8192) p (by omega),
        writeW_outside _ _ _ (by omega : x + 4 * n + 4 ≤ 8192) p (by omega)]
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hi => by omega, fun _ hi => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86
