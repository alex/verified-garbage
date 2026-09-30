import VerifiedGarbage.Proof.X448.X86_64.Copy

/-!
# X448 on x86-64: constant-time conditional swaps

Untrusted: everything here is checked by Lean. An XOR mask exchanges the
limbs without a branch or an address depending on the swap bit.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

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
    (hx : Slot x) (hy : Slot y) (hi : i < 16) {sw : Bool} (hc : s.gpr .rcx = mask sw) :
    WP isa (.block
      [.mov .rax (.mem (sc (x + 8 * i))), .mov .rdx (.mem (sc (y + 8 * i))),
        .mov .r8 (.reg .rax), .alu .xor .r8 (.reg .rdx), .alu .and .r8 (.reg .rcx),
        .alu .xor .rax (.reg .r8), .alu .xor .rdx (.reg .r8),
        .store (sc (x + 8 * i)) .rax, .store (sc (y + 8 * i)) .rdx]) s fun t =>
      t.mem = (s.mem.writeW (off base (x + 8 * i))
        (if sw then word s.mem base (y + 8 * i) else word s.mem base (x + 8 * i))).writeW
        (off base (y + 8 * i)) (if sw then word s.mem base (x + 8 * i) else word s.mem base (y + 8 * i)) ∧
      Keeps [.rax, .rdx, .r8] s t := by
  have lx := hs.read (d := x + 8 * i) (n := 8) (by change x + 128 ≤ 3584 at hx; omega)
  have ly := hs.read (d := y + 8 * i) (n := 8) (by change y + 128 ≤ 3584 at hy; omega)
  have wx := hs.write (d := x + 8 * i) (n := 8) (by change x + 128 ≤ 3584 at hx; omega)
  have wy := hs.write (d := y + 8 * i) (n := 8) (by change y + 128 ≤ 3584 at hy; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, ea_sc,
    State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, hs.rdi, hc, lx, ly, wx, wy, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  simp only [(xor_sel sw _ _).1, (xor_sel sw _ _).2]
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]

/-- Reading two disjoint words after writing a limb pair. -/
theorem pair_write {m : Mem} {base : Addr} {x y n j : Nat} (hx : Slot x) (hy : Slot y)
    (hxy : x + 128 ≤ y ∨ y + 128 ≤ x) (hn : n < 16) (hj : j < 16) (vx vy : BitVec 64) :
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

/-- Swap all sixteen limbs under the mask, preserving all other bytes. -/
theorem cswap_ok {s : State} {base : Addr} (hs : Scr s base) {x y : Nat} (hx : Slot x) (hy : Slot y)
    (hxy : x + 128 ≤ y ∨ y + 128 ≤ x) {sw : Bool} (hc : s.gpr .rcx = mask sw) :
    WP isa (.block (cswap x y)) s fun t =>
      (∀ i < 16, limbs t.mem base x i = if sw then limbs s.mem base y i else limbs s.mem base x i) ∧
      (∀ i < 16, limbs t.mem base y i = if sw then limbs s.mem base x i else limbs s.mem base y i) ∧
      Outside2 base x 128 y 128 s.mem t.mem ∧ Keeps [.rax, .rdx, .r8] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base x i = if sw then limbs s.mem base y i else limbs s.mem base x i) ∧
    (∀ i < n, limbs t.mem base y i = if sw then limbs s.mem base x i else limbs s.mem base y i) ∧
    Outside2 base x (8 * n) y (8 * n) s.mem t.mem ∧ Keeps [.rax, .rdx, .r8] s t
  have xb : x + 128 ≤ 8192 := Nat.le_trans hx (by decide)
  have yb : y + 128 ≤ 8192 := Nat.le_trans hy (by decide)
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block
      [.mov .rax (.mem (sc (x + 8 * n))), .mov .rdx (.mem (sc (y + 8 * n))),
        .mov .r8 (.reg .rax), .alu .xor .r8 (.reg .rdx), .alu .and .r8 (.reg .rcx),
        .alu .xor .rax (.reg .r8), .alu .xor .rdx (.reg .r8),
        .store (sc (x + 8 * n)) .rax, .store (sc (y + 8 * n)) .rdx]) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tc := (tk.1 .rcx (by decide)).trans hc
    refine WP.mono (swapStep_ok (hs.of_keeps tk (by decide)) hx hy hn tc) fun u ⟨um, uk⟩ => ?_
    have ex : limbs t.mem base x n = limbs s.mem base x n :=
      congrArg BitVec.toNat (tm.word (by omega) (by omega) (by omega))
    have ey : limbs t.mem base y n = limbs s.mem base y n :=
      congrArg BitVec.toNat (tm.word (by omega) (by omega) (by omega))
    have pair := fun (j : Nat) (hj : j < 16) => pair_write (m := t.mem) (base := base) hx hy hxy hn hj
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
  exact wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) s
    ⟨fun _ hi => by omega, fun _ hi => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86_64
