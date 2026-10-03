import VerifiedGarbage.Proof.X448.X86_64.Chain

/-!
# X448 on x86-64: products by columns

A product's term (`term_ok`): `x · y` (twice if doubled) added to a
three-word accumulator; a column's terms (`terms_ok`), by induction on them;
and the fourteen columns (`columns_ok`), by induction on the columns, each
storing its low word at `ACC` and passing the rest of its accumulator on, in
the registers `accR` rotated. Then the columns of `mul` and `sqr` sum to the
product and the square (`mulCols_sum`, `sqrCols_sum`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

/-- The registers a product's columns change. -/
def colX : List Reg := [.rax, .rdx, .r15, .rcx, .rbp]

/-- `x · y` in two words (`mul`). -/
theorem mul_halves (a b : BitVec 64) :
    (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat +
        2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat = a.toNat * b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hp : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ / 2 ^ 64) (by omega)]
  omega

/-- `rax = x`, then `rdx:rax = x · y`. -/
theorem mov_mul_ok (s : State) {x : Src} {y : Reg} {vx : BitVec 64} (hx : readSrc s x = some vx)
    (hy : y ≠ .rax) :
    WP isa (.block [.mov .rax x, .mul y]) s fun s' =>
      (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rdx).toNat = vx.toNat * (s.gpr y).toNat ∧
      Keeps [.rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hx, Option.map_some, execMul,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ hy, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact mul_halves vx (s.gpr y)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr.2, RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setFlags,
      RegUpd.gpr_setReg_of_ne _ _ hr.1]

/-- `r0–r2 += rdx:rax`. -/
theorem acc_ok (s : State) {r0 r1 r2 : Reg} (hd : [r0, r1, r2, .rax, .rdx].Nodup)
    (hb : rv s [r0, r1, r2] + ((s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rdx).toNat) < 2 ^ 192) :
    WP isa (.block [.alu .add r0 (.reg .rax), .alu .adc r1 (.reg .rdx), .alu .adc r2 (.imm 0)]) s
      fun s' => rv s' [r0, r1, r2] =
          rv s [r0, r1, r2] + ((s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rdx).toNat) ∧
        Keeps [r0, r1, r2] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h0a, h0d⟩, ⟨h12, h1a, h1d⟩, ⟨h2a, h2d⟩, -⟩ := hd
  refine WP.mono (add_chain_ok [r0, r1, r2] s r0 [r1, r2] (.reg .rax) [.reg .rdx, .imm 0]
    (s.gpr .rax) [s.gpr .rdx, 0] (fun _ h => h) (by simp [h01, h02, h12]) rfl
    (stable_reg s (by simp [Ne.symm h0a, Ne.symm h1a, Ne.symm h2a]))
    (.cons (stable_reg s (by simp [Ne.symm h0d, Ne.symm h1d, Ne.symm h2d]))
      (.cons (stable_imm0 _ _) .nil))) fun s' ⟨c, _, he, hk⟩ => ⟨?_, hk⟩
  have hl : 64 * [r0, r1, r2].length = 192 := rfl
  rw [hl] at he
  simp only [wv, toNat_zero64] at he
  have := Bool.toNat_le c
  rcases Nat.lt_or_ge c.toNat 1 with h | h <;> omega

/-- A term's weight: 2 if it is doubled. -/
def termK (t : Term) : Nat := if t.dbl then 2 else 1

/-- A term's value. -/
def tv (xv yv : Nat → Nat) (t : Term) : Nat := termK t * (xv t.i * yv t.j)

/-- `term`: `r0–r2 += x · y`, twice if `dbl`. -/
theorem term_ok (s : State) {x : Src} {y r0 r1 r2 : Reg} {vx : BitVec 64} (dbl : Bool)
    (hx : readSrc s x = some vx) (hy : y ≠ .rax) (hd : [r0, r1, r2, .rax, .rdx].Nodup)
    (hb : rv s [r0, r1, r2] + (if dbl then 2 else 1) * (vx.toNat * (s.gpr y).toNat) < 2 ^ 192) :
    WP isa (.block (term x y r0 r1 r2 dbl)) s fun s' =>
      rv s' [r0, r1, r2] = rv s [r0, r1, r2] + (if dbl then 2 else 1) * (vx.toNat * (s.gpr y).toNat) ∧
      Keeps [.rax, .rdx, r0, r1, r2] s s' := by
  have hd' := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd'
  obtain ⟨⟨_, _, h0a, h0d⟩, ⟨_, h1a, h1d⟩, ⟨h2a, h2d⟩, -⟩ := hd'
  rw [term, List.append_assoc, WP.block_append_iff]
  refine WP.mono (mov_mul_ok s hx hy) fun s1 ⟨e1, k1⟩ => ?_
  have r1 : rv s1 [r0, r1, r2] = rv s [r0, r1, r2] := k1.rv_eq (by simp [h0a, h1a, h2a, h0d, h1d, h2d])
  have hp := Nat.zero_le (vx.toNat * (s.gpr y).toNat)
  cases dbl with
  | false =>
    simp only [Bool.false_eq_true, ite_false, List.nil_append, Nat.one_mul] at hb ⊢
    refine WP.mono (acc_ok s1 hd (by omega)) fun s2 ⟨e2, k2⟩ => ⟨by omega, ?_⟩
    exact (k1.mono (by simp)).trans (k2.mono (by simp))
  | true =>
    simp only [ite_true] at hb ⊢
    rw [WP.block_append_iff]
    refine WP.mono (acc_ok s1 hd (by omega)) fun s2 ⟨e2, k2⟩ => ?_
    have a2 : s2.gpr .rax = s1.gpr .rax := k2.1 _ (by simp [Ne.symm h0a, Ne.symm h1a, Ne.symm h2a])
    have d2 : s2.gpr .rdx = s1.gpr .rdx := k2.1 _ (by simp [Ne.symm h0d, Ne.symm h1d, Ne.symm h2d])
    refine WP.mono (acc_ok s2 hd (by rw [a2, d2]; omega)) fun s3 ⟨e3, k3⟩ => ⟨?_, ?_⟩
    · rw [a2, d2] at e3; omega
    · exact ((k1.mono (by simp)).trans (k2.mono (by simp))).trans (k3.mono (by simp))

/-- The sum of a column's terms. -/
def colSum (xv yv : Nat → Nat) (ts : List Term) : Nat := (ts.map (tv xv yv)).sum

theorem colSum_cons (xv yv : Nat → Nat) (t : Term) (ts : List Term) :
    colSum xv yv (t :: ts) = termK t * (xv t.i * yv t.j) + colSum xv yv ts := by
  simp [colSum, tv]

/-- A column's terms, by induction on them. -/
theorem terms_ok (x : Nat → Src) (y : Nat → Reg) (xv : Nat → BitVec 64) {r0 r1 r2 : Reg}
    (hd : [r0, r1, r2, .rax, .rdx].Nodup) :
    ∀ (ts : List Term) (s : State),
      (∀ t ∈ ts, Stable [.rax, .rdx, r0, r1, r2] s (x t.i) (xv t.i)) →
      (∀ t ∈ ts, y t.j ∉ [.rax, .rdx, r0, r1, r2]) →
      rv s [r0, r1, r2] + colSum (fun i => (xv i).toNat) (fun j => (s.gpr (y j)).toNat) ts < 2 ^ 192 →
      WP isa (.block (ts.flatMap fun t => term (x t.i) (y t.j) r0 r1 r2 t.dbl)) s fun s' =>
        rv s' [r0, r1, r2] = rv s [r0, r1, r2] +
          colSum (fun i => (xv i).toNat) (fun j => (s.gpr (y j)).toNat) ts ∧
        Keeps [.rax, .rdx, r0, r1, r2] s s'
  | [], s, _, _, _ => WP.block_nil ⟨by simp [colSum], Keeps.refl _ _⟩
  | t :: ts, s, hx, hy, hb => by
    rw [List.flatMap_cons, WP.block_append_iff]
    have hyt := hy t List.mem_cons_self
    rw [colSum_cons] at hb
    simp only [termK] at hb
    refine WP.mono (term_ok s t.dbl (hx t List.mem_cons_self).read
      (fun e => hyt (by simp [e])) hd (by omega)) fun s1 ⟨e1, k1⟩ => ?_
    have gy : ∀ t' ∈ t :: ts, s1.gpr (y t'.j) = s.gpr (y t'.j) := fun t' ht' => k1.1 _ (hy t' ht')
    have cs : colSum (fun i => (xv i).toNat) (fun j => (s1.gpr (y j)).toNat) ts =
        colSum (fun i => (xv i).toNat) (fun j => (s.gpr (y j)).toNat) ts := by
      simp only [colSum]
      exact congrArg List.sum (List.map_congr_left fun t' ht' => by
        simp only [tv, gy t' (List.mem_cons_of_mem _ ht')])
    refine WP.mono (terms_ok x y xv hd ts s1
      (fun t' ht' => (hx t' (List.mem_cons_of_mem _ ht')).of_keeps k1)
      (fun t' ht' => hy t' (List.mem_cons_of_mem _ ht')) (by rw [cs, e1]; omega))
      fun s2 ⟨e2, k2⟩ => ⟨?_, k1.trans k2⟩
    rw [e2, cs, e1, colSum_cons]
    simp only [termK]
    omega

/-! ## Columns -/

/-- The accumulator of column `k`. -/
def acc (k : Nat) : List Reg := [accR k 0, accR k 1, accR k 2]

theorem accR_mod (k n : Nat) : accR k n = [Reg.r15, .rcx, .rbp].getD ((k + n) % 3) .r15 := rfl

theorem acc_succ (k : Nat) : acc (k + 1) = [accR k 1, accR k 2, accR k 0] := by
  simp only [acc, accR_mod]
  refine List.cons_eq_cons.mpr ⟨by rw [Nat.add_right_comm], List.cons_eq_cons.mpr
    ⟨by rw [Nat.add_assoc], List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩
  rw [show k + 1 + 2 = k + 3 by omega, Nat.add_mod_right, Nat.add_zero]

theorem acc_cases (k : Nat) :
    acc k = [.r15, .rcx, .rbp] ∨ acc k = [.rcx, .rbp, .r15] ∨ acc k = [.rbp, .r15, .rcx] := by
  simp only [acc, accR_mod]
  have h := Nat.mod_lt k (show 0 < 3 by decide)
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h <;>
  simp only [Nat.add_mod k, h] <;> simp

theorem acc_nodup (k : Nat) : [accR k 0, accR k 1, accR k 2, .rax, .rdx].Nodup := by
  have := acc_cases k
  simp only [acc, List.cons.injEq, and_true] at this
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> decide

theorem acc_colX (k : Nat) : ∀ r ∈ [Reg.rax, .rdx, accR k 0, accR k 1, accR k 2], r ∈ colX := by
  have := acc_cases k
  simp only [acc, List.cons.injEq, and_true] at this
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> decide

theorem accR_colX (k n : Nat) (hn : n < 3) : accR k n ∈ colX := by
  have := acc_colX k
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;> exact this _ (by simp)

theorem rdi_colX : Reg.rdi ∉ colX := by decide

/-- A column: its terms, its low word stored at `ACC + 8k`, and the rest of
the accumulator passed on. -/
theorem column_ok {s : State} {base : Addr} (hs : Scr s base) (x : Nat → Src) (y : Nat → Reg)
    (xv : Nat → BitVec 64) (ts : List Term) (k : Nat) (hk : ACC + 8 * k + 8 ≤ 8192)
    (hx : ∀ t ∈ ts, Stable colX s (x t.i) (xv t.i)) (hy : ∀ t ∈ ts, y t.j ∉ colX)
    (hb : rv s (acc k) + colSum (fun i => (xv i).toNat) (fun j => (s.gpr (y j)).toNat) ts <
      2 ^ 192) :
    WP isa (.block (column x y ts k)) s fun s' =>
      (word s'.mem base (ACC + 8 * k)).toNat + 2 ^ 64 * rv s' (acc (k + 1)) =
        rv s (acc k) + colSum (fun i => (xv i).toNat) (fun j => (s.gpr (y j)).toNat) ts ∧
      (∀ r, r ∉ colX → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base (ACC + 8 * k) 8 s.mem s'.mem := by
  have hsub := acc_colX k
  rw [column, WP.block_append_iff]
  refine WP.mono (terms_ok x y xv (acc_nodup k) ts s (fun t ht => (hx t ht).mono hsub)
    (fun t ht h => hy t ht (hsub _ h)) hb) fun s1 ⟨e1, k1⟩ => ?_
  have hs1 : Scr s1 base := hs.of_keeps k1 (fun h => rdi_colX (hsub _ h))
  have hw := hs1.write (d := ACC + 8 * k) (n := 8) hk
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_sc, hs1.rdi, State.store64, hw,
    ite_true, readSrc32, Option.map_some, State.setReg32, Option.some.injEq,
    exists_eq_left']
  have hn := acc_nodup k
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨⟨h01, h02, -, -⟩, ⟨h12, -, -⟩, -, -⟩ := hn
  refine ⟨?_, fun r hr => ?_, k1.2.2.1, k1.2.2.2, ?_⟩
  · rw [acc_succ]
    simp only [rv, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm h01),
      RegUpd.gpr_setReg_of_ne _ _ (Ne.symm h02)]
    rw [RegUpd.mem_setReg]
    simp only [word_writeW_self]
    simp only [acc, rv] at e1 ⊢
    have z : (BitVec.setWidth 64 (0 : BitVec 32)).toNat = 0 := rfl
    rw [z]
    omega
  · have hr0 : r ≠ accR k 0 := fun e => hr (e ▸ accR_colX k 0 (by decide))
    rw [RegUpd.gpr_setReg_of_ne _ _ hr0]
    exact k1.1 r (fun h => hr (hsub _ h))
  · rw [← k1.2.1]; exact writeW_outside _ _ _ (by omega)

theorem mv_succ_last (m : Mem) (base : Addr) :
    ∀ (o n : Nat), mv m base o (n + 1) = mv m base o n + 2 ^ (64 * n) * (word m base (o + 8 * n)).toNat
  | o, 0 => by simp [mv]
  | o, n + 1 => by
    rw [mv, mv_succ_last m base (o + 8) n, mv, pow64_succ,
      show o + 8 + 8 * n = o + 8 * (n + 1) by omega]
    generalize 2 ^ (64 * n) = Q
    grind

/-- The columns' values: `Σ_{m<n} 2^(64m) colSum (cols (k + m))`, in Horner
form, whose only power is `2⁶⁴`. -/
def colsVal (xv yv : Nat → Nat) (cols : Nat → List Term) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => colSum xv yv (cols k) + 2 ^ 64 * colsVal xv yv cols (k + 1) n

theorem colsVal_succ_last (xv yv : Nat → Nat) (cols : Nat → List Term) :
    ∀ k n, colsVal xv yv cols k (n + 1) =
      colsVal xv yv cols k n + 2 ^ (64 * n) * colSum xv yv (cols (k + n))
  | k, 0 => by simp [colsVal]
  | k, n + 1 => by
    rw [colsVal, colsVal_succ_last xv yv cols (k + 1) n, colsVal, pow64_succ,
      show k + 1 + n = k + (n + 1) by omega]
    generalize 2 ^ (64 * n) = Q
    grind

theorem colSum_le (xv yv : Nat → Nat) :
    ∀ ts : List Term, (∀ t ∈ ts, xv t.i < 2 ^ 64 ∧ yv t.j < 2 ^ 64) →
      colSum xv yv ts ≤ (ts.map termK).sum * ((2 ^ 64 - 1) * (2 ^ 64 - 1))
  | [], _ => by simp [colSum]
  | t :: ts, h => by
    rw [colSum_cons, List.map_cons, List.sum_cons, Nat.add_mul]
    have h1 := h t List.mem_cons_self
    have hp : xv t.i * yv t.j ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.mul_le_mul_left (termK t) hp
    have := colSum_le xv yv ts fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    omega

theorem colSum_congr (xv yv yv' : Nat → Nat) (ts : List Term) (h : ∀ t ∈ ts, yv t.j = yv' t.j) :
    colSum xv yv ts = colSum xv yv' ts := by
  simp only [colSum]
  exact congrArg List.sum (List.map_congr_left fun t ht => by simp only [tv, h t ht])

/-- The first `n` columns of a product. -/
theorem columns_ok {s₀ : State} {base : Addr} (hs : Scr s₀ base) (x : Nat → Src) (y : Nat → Reg)
    (xv : Nat → BitVec 64) (cols : Nat → List Term)
    (hx : ∀ s, (∀ r, r ∉ colX → s.gpr r = s₀.gpr r) → s.rd = s₀.rd → s.wr = s₀.wr →
      Outside base ACC 112 s₀.mem s.mem → ∀ i < 7, Stable colX s (x i) (xv i))
    (hy : ∀ j < 7, y j ∉ colX) (hc : ∀ k < 14, ∀ t ∈ cols k, t.i < 7 ∧ t.j < 7)
    (hw : ∀ k < 14, ((cols k).map termK).sum ≤ 7) (h0 : rv s₀ (acc 0) = 0) :
    ∀ n ≤ 14, WP isa (.block ((List.range n).flatMap fun k => column x y (cols k) k)) s₀ fun s =>
      (∀ r, r ∉ colX → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
      Outside base ACC (8 * n) s₀.mem s.mem ∧
      mv s.mem base ACC n + 2 ^ (64 * n) * rv s (acc n) =
        colsVal (fun i => (xv i).toNat) (fun j => (s₀.gpr (y j)).toNat) cols 0 n ∧
      rv s (acc n) < 2 ^ 128
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _, by simp [mv, colsVal, h0],
      by rw [h0]; decide⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (columns_ok hs x y xv cols hx hy hc hw h0 n (by omega))
      fun s ⟨g, rd, wr, o, e, b⟩ => ?_
    have hsS : Scr s base := ⟨(g _ rdi_colX).trans hs.rdi, wr ▸ hs.wr, hs.nowrap⟩
    have hxs := hx s g rd wr (o.mono (by omega) (by omega))
    have hcn := hc n (by omega)
    have gy : ∀ t ∈ cols n, (s.gpr (y t.j)).toNat = (s₀.gpr (y t.j)).toNat :=
      fun t ht => by rw [g _ (hy _ (hcn t ht).2)]
    have cs := colSum_congr (fun i => (xv i).toNat) (fun j => (s.gpr (y j)).toNat)
      (fun j => (s₀.gpr (y j)).toNat) (cols n) gy
    have cb := colSum_le (fun i => (xv i).toNat) (fun j => (s.gpr (y j)).toNat) (cols n)
      fun t _ => ⟨(xv t.i).isLt, (s.gpr (y t.j)).isLt⟩
    have hwn := Nat.mul_le_mul_right ((2 ^ 64 - 1) * (2 ^ 64 - 1)) (hw n (by omega))
    rw [List.flatMap_singleton]
    refine WP.mono (column_ok hsS x y xv (cols n) n (by simp only [ACC]; omega)
      (fun t ht => hxs t.i (hcn t ht).1) (fun t ht => hy _ (hcn t ht).2) (by omega))
      fun s' ⟨e', g', rd', wr', o'⟩ => ?_
    refine ⟨fun r hr => (g' r hr).trans (g r hr), rd'.trans rd, wr'.trans wr,
      (o.mono (Nat.le_refl _) (by omega)).trans (o'.mono (by omega) (by omega)), ?_, ?_⟩
    · rw [mv_succ_last, o'.mv (d := ACC) (k := n) (by omega) (by simp only [ACC]; omega),
        colsVal_succ_last, Nat.zero_add, pow64_succ, ← cs]
      rw [cs] at e'
      generalize 2 ^ (64 * n) = Q at e ⊢
      calc mv s.mem base ACC n + Q * (word s'.mem base (ACC + 8 * n)).toNat +
            2 ^ 64 * Q * rv s' (acc (n + 1))
          = mv s.mem base ACC n + Q * ((word s'.mem base (ACC + 8 * n)).toNat +
              2 ^ 64 * rv s' (acc (n + 1))) := by grind
        _ = mv s.mem base ACC n + Q * rv s (acc n) + Q * colSum (fun i => (xv i).toNat)
              (fun j => (s₀.gpr (y j)).toNat) (cols n) := by rw [e']; grind
        _ = _ := by rw [e, cs]
    · omega

/-! ## The columns of `mul` and `sqr` -/

/-- Seven words' value, in Horner form. -/
def val7 (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 64 * (f 1 + 2 ^ 64 * (f 2 + 2 ^ 64 * (f 3 + 2 ^ 64 * (f 4 + 2 ^ 64 * (f 5 +
    2 ^ 64 * f 6)))))

theorem mulCol_hc : ∀ k < 14, ∀ t ∈ mulCol k, t.i < 7 ∧ t.j < 7 := by decide
theorem mulCol_hw : ∀ k < 14, ((mulCol k).map termK).sum ≤ 7 := by decide
theorem sqrCol_hc : ∀ k < 14, ∀ t ∈ sqrCol k, t.i < 7 ∧ t.j < 7 := by decide
theorem sqrCol_hw : ∀ k < 14, ((sqrCol k).map termK).sum ≤ 7 := by decide

theorem range7 : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := rfl

theorem mulCols_sum (xv yv : Nat → Nat) : colsVal xv yv mulCol 0 14 = val7 xv * val7 yv := by
  simp (config := {decide := true}) only [colsVal, colSum, mulCol, range7, List.filter_cons,
    List.filter_nil, ite_true, ite_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    tv, termK, val7, Nat.reduceAdd, Nat.reduceSub, Nat.one_mul]
  generalize 2 ^ 64 = B
  grind

theorem sqrCols_sum (xv : Nat → Nat) : colsVal xv xv sqrCol 0 14 = val7 xv * val7 xv := by
  simp (config := {decide := true}) only [colsVal, colSum, sqrCol, range7, List.filter_cons,
    List.filter_nil, ite_true, ite_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    tv, termK, val7, Nat.reduceAdd, Nat.reduceSub, Nat.one_mul, List.append_nil, List.cons_append,
    List.nil_append, Nat.reduceDiv]
  generalize 2 ^ 64 = B
  grind

theorem mv7 (m : Mem) (base : Addr) (o : Nat) :
    mv m base o 7 = val7 fun i => (word m base (o + 8 * i)).toNat := by
  simp only [mv, val7, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero, Nat.mul_zero]

theorem rvW (s : State) : rv s W = val7 fun i => (s.gpr (w i)).toNat := by
  simp only [rv, W, val7, w, List.getD_cons_succ, List.getD_cons_zero, Nat.mul_zero, Nat.add_zero]

end VG.Proof.X448.X86_64
