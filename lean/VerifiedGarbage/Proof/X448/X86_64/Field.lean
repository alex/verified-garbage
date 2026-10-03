import VerifiedGarbage.Proof.X448.X86_64.Reduce

/-!
# X448 on x86-64: the field multiplications

Each field operation on the working space as a change of the field element
`F` it writes: the element at `o` becomes the result, the bytes outside it
and the product's words at `ACC` are unchanged, and so are the registers but
those the arithmetic uses (`Op`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448
open VG.Spec.X448 (P)

/-- The field element at `base + o`, in `GF(p)`. -/
abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe := toFe (fe m base o)

/-- A field element's slot: below the product's words. -/
abbrev Slot (o : Nat) : Prop := o + 56 ≤ ACC

/-- A field operation's effect but for its result: the registers but `clob`,
the regions and the memory outside the 56 bytes at `base + o` and the
product's words are unchanged. -/
structure Op (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside2 base o 56 ACC 112 s.mem s'.mem

theorem Op.scr {base : Addr} {o : Nat} {s s' : State} (h : Op base o s s') (hs : Scr s base) :
    Scr s' base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem mv_add (m : Mem) (base : Addr) :
    ∀ (o a b : Nat), mv m base o (a + b) = mv m base o a + 2 ^ (64 * a) * mv m base (o + 8 * a) b
  | o, 0, b => by simp [mv]
  | o, a + 1, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega, mv, mv, mv_add m base (o + 8) a b, pow64_succ,
      show o + 8 + 8 * a = o + 8 * (a + 1) by omega]
    ring

theorem zeroAcc_ok (s : State) :
    WP isa (.block zeroAcc) s fun s' => rv s' (acc 0) = 0 ∧ Keeps [.r15, .rcx, .rbp] s s' := by
  apply WP.of_runBlock
  simp only [zeroAcc, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [acc, accR_mod, Nat.zero_add, Nat.reduceMod, List.getD_cons_zero,
      List.getD_cons_succ, rv, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The product of an `a`-word and a `b`-word number has `a + b` words.
(Exponents are kept symbolic: Lean does not evaluate powers above `2²⁵⁶`.) -/
theorem prod_lt {x y a b : Nat} (hx : x < 2 ^ (64 * a)) (hy : y < 2 ^ (64 * b)) :
    x * y < 2 ^ (64 * (a + b)) := by
  rw [Nat.mul_add, Nat.pow_add]
  exact Nat.mul_lt_mul'' hx hy

/-- The columns and the reduction of a product `x · y`: given the columns'
result (`hcol`), `[o] ≡ x · y`. -/
theorem product_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : Slot o)
    {x y : Nat} (hx : x < 2 ^ (64 * 7)) (hy : y < 2 ^ (64 * 7))
    (hcol : mv s.mem base ACC (7 + 7) + 2 ^ (64 * (7 + 7)) * rv s (acc (7 + 7)) = x * y) :
    WP isa (.block (reduce o)) s fun s' =>
      fe s'.mem base o % P = x * y % P ∧
      (∀ r, r ∉ clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base o 56 s.mem s'.mem := by
  refine WP.mono (reduce_ok hs ho) fun s' ⟨e, g, rd, wr, out⟩ => ⟨?_, g, rd, wr, out⟩
  have hl := prod_lt hx hy
  have h0 : rv s (acc (7 + 7)) = 0 := by
    rcases Nat.eq_zero_or_pos (rv s (acc (7 + 7))) with h | h
    · exact h
    · exfalso
      have := Nat.mul_le_mul_left (2 ^ (64 * (7 + 7))) h
      generalize 2 ^ (64 * (7 + 7)) = Q at *
      omega
  rw [h0, Nat.mul_zero, Nat.add_zero, mv_add] at hcol
  rw [e, ← hcol]

theorem val7_congr {f g : Nat → Nat} (h : ∀ i < 7, f i = g i) : val7 f = val7 g := by
  simp only [val7, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide)]

theorem colX_clob : ∀ r ∈ colX, r ∈ clob := by decide
theorem acc_clob : ∀ r ∈ [Reg.r15, .rcx, .rbp], r ∈ clob := by decide
theorem w_acc : ∀ j < 7, w j ∉ [Reg.r15, .rcx, .rbp] := by decide
theorem W_clob : ∀ r ∈ W, r ∈ clob := by decide

/-- The end of `mul` and `sqr`: the columns, then the reduction, with the
columns' operands `xv`, `yv` whose values are `x` and `y`. -/
theorem colsReduce_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : Slot o)
    (xs : Nat → Src) (xv : Nat → BitVec 64) (cols : Nat → List Term)
    (hx : ∀ s', (∀ r, r ∉ colX → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Outside base ACC 112 s.mem s'.mem → ∀ i < 7, Stable colX s' (xs i) (xv i))
    (hc : ∀ k < 14, ∀ t ∈ cols k, t.i < 7 ∧ t.j < 7) (hw : ∀ k < 14, ((cols k).map termK).sum ≤ 7)
    (h0 : rv s (acc 0) = 0) {x y : Nat} (hxl : x < 2 ^ (64 * 7)) (hyl : y < 2 ^ (64 * 7))
    (hsum : colsVal (fun i => (xv i).toNat) (fun j => (s.gpr (w j)).toNat) cols 0 14 = x * y) :
    WP isa (.block (columns xs w cols ++ reduce o)) s fun s' =>
      fe s'.mem base o % P = x * y % P ∧ (∀ r, r ∉ clob → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside2 base o 56 ACC 112 s.mem s'.mem := by
  rw [WP.block_append_iff, columns]
  refine WP.mono (columns_ok hs xs w xv cols hx (by decide) hc hw h0 (7 + 7) le_rfl)
    fun s1 ⟨g1, rd1, wr1, o1, e1, _⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ rdi_colX).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (product_ok hs1 ho hxl hyl (by rw [e1]; exact hsum)) fun s2 ⟨e2, g2, rd2, wr2, o2⟩ =>
    ⟨e2, fun r hr => (g2 r hr).trans (g1 r fun h => hr (colX_clob r h)), rd2.trans rd1, wr2.trans wr1,
      (o1.right o 56).trans (o2.left ACC 112)⟩

/-- `[o] = [a] · [b]`. -/
theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mul o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b := by
  have ha' : a + 56 ≤ 1536 := ha
  have hb' : b + 56 ≤ 1536 := hb
  rw [mul, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok hs b W W_nodup (by decide)
    (by rw [show W.length = 7 from rfl]; omega)) fun s1 ⟨w1, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeroAcc_ok s1) fun s2 ⟨z2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  have m2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  refine WP.mono (colsReduce_ok hs2 ho (fun i => .mem (sc (a + 8 * i)))
    (fun i => word s2.mem base (a + 8 * i)) mulCol
    (fun s' g _ wr out i hi => by
      have hsS : Scr s' base := ⟨(g _ rdi_colX).trans hs2.rdi, wr ▸ hs2.wr, hs2.nowrap⟩
      have := stable_sc hsS rdi_colX (d := a + 8 * i) (by omega)
      rwa [out.word (by simp only [ACC]; omega) (by omega)] at this)
    mulCol_hc mulCol_hw z2 (mv_lt s.mem base a 7) (mv_lt s.mem base b 7) ?_)
    fun s' ⟨e, g, rd, wr, out⟩ => ⟨⟨fun r hr => ?_, rd.trans (k2.2.2.1.trans k1.2.2.1),
      wr.trans (k2.2.2.2.trans k1.2.2.2), by rw [← m2]; exact out⟩, ?_⟩
  · rw [mulCols_sum, mv7, mv7, m2]
    refine congrArg (val7 _ * ·) (val7_congr fun j hj => ?_)
    rw [k2.1 _ (w_acc j hj)]
    exact congrArg BitVec.toNat (w1 j hj .r8)
  · rw [g r hr, k2.1 r (fun h => hr (acc_clob r h)),
      k1.1 r (fun h => hr (W_clob r h))]
  · exact toFe_mul e

theorem w_colX : ∀ j < 7, w j ∉ colX := by decide

/-- `[o] = [a]²`. -/
theorem sqr_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqr o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a := by
  have ha' : a + 56 ≤ 1536 := ha
  rw [sqr, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok hs a W W_nodup (by decide)
    (by rw [show W.length = 7 from rfl]; omega)) fun s1 ⟨w1, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeroAcc_ok s1) fun s2 ⟨z2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  have m2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have v2 : val7 (fun j => (s2.gpr (w j)).toNat) = fe s.mem base a := by
    rw [fe, mv7]
    refine val7_congr fun j hj => ?_
    rw [k2.1 _ (w_acc j hj)]
    exact congrArg BitVec.toNat (w1 j hj .r8)
  refine WP.mono (colsReduce_ok hs2 ho (fun i => .reg (w i)) (fun i => s2.gpr (w i)) sqrCol
    (fun s' g _ _ _ i hi => by
      have := stable_reg (X := colX) s' (w_colX i hi)
      rwa [g _ (w_colX i hi)] at this)
    sqrCol_hc sqrCol_hw z2 (mv_lt s.mem base a 7) (mv_lt s.mem base a 7)
    (by rw [sqrCols_sum, v2]))
    fun s' ⟨e, g, rd, wr, out⟩ => ⟨⟨fun r hr => ?_, rd.trans (k2.2.2.1.trans k1.2.2.1),
      wr.trans (k2.2.2.2.trans k1.2.2.2), by rw [← m2]; exact out⟩, toFe_mul e⟩
  rw [g r hr, k2.1 r (fun h => hr (acc_clob r h)), k1.1 r (fun h => hr (W_clob r h))]

end VG.Proof.X448.X86_64
