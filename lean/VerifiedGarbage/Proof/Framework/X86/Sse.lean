import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.TCB.X86.Isa

/-!
# x86 (32-bit): SSE values as doublewords

The SSE instructions of the model, stated on the doublewords of their operands
(`dword`, `ofDwords`), and 128-bit loads and stores as four 32-bit words.
-/

namespace VG.X86


theorem getLsbD_ofDwords (a b c d : BitVec 32) (i : Nat) :
    (ofDwords a b c d).getLsbD i =
      if i < 32 then a.getLsbD i else if i - 32 < 32 then b.getLsbD (i - 32) else
      if i - 32 - 32 < 32 then c.getLsbD (i - 32 - 32) else d.getLsbD (i - 32 - 32 - 32) := by
  unfold ofDwords
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append]

theorem getLsbD_dword (x : BitVec 128) (k i : Nat) :
    (dword x k).getLsbD i = (decide (i < 32) && x.getLsbD (32 * k + i)) := by
  simp only [dword, BitVec.getLsbD_extractLsb']

@[simp] theorem dword_ofDwords_0 (a b c d : BitVec 32) : dword (ofDwords a b c d) 0 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp (disch := omega) only [getLsbD_dword, getLsbD_ofDwords, decide_eq_true hi, Bool.true_and,
    ite_eq_left, Nat.mul_zero, Nat.zero_add]

@[simp] theorem dword_ofDwords_1 (a b c d : BitVec 32) : dword (ofDwords a b c d) 1 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp (disch := omega) only [getLsbD_dword, getLsbD_ofDwords, decide_eq_true hi, Bool.true_and,
    ite_eq_left, ite_eq_right, show 32 * 1 + i - 32 = i by omega]

@[simp] theorem dword_ofDwords_2 (a b c d : BitVec 32) : dword (ofDwords a b c d) 2 = c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp (disch := omega) only [getLsbD_dword, getLsbD_ofDwords, decide_eq_true hi, Bool.true_and,
    ite_eq_left, ite_eq_right, show 32 * 2 + i - 32 - 32 = i by omega]

@[simp] theorem dword_ofDwords_3 (a b c d : BitVec 32) : dword (ofDwords a b c d) 3 = d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp (disch := omega) only [getLsbD_dword, getLsbD_ofDwords, decide_eq_true hi, Bool.true_and,
    ite_eq_right, show 32 * 3 + i - 32 - 32 - 32 = i by omega]

theorem ofDwords_dword (x : BitVec 128) :
    ofDwords (dword x 0) (dword x 1) (dword x 2) (dword x 3) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_ofDwords]
  simp only [getLsbD_dword]
  by_cases h1 : i < 32
  · simp only [h1, ite_true, decide_true, Bool.true_and] <;> exact congrArg _ (by omega)
  by_cases h2 : i < 64
  · simp only [h1, show i - 32 < 32 by omega, ite_true, ite_false, decide_true,
      Bool.true_and] <;> exact congrArg _ (by omega)
  by_cases h3 : i < 96
  · simp only [h1, show ¬ i - 32 < 32 by omega, show i - 32 - 32 < 32 by omega, ite_true, ite_false,
      decide_true, Bool.true_and] <;> exact congrArg _ (by omega)
  · simp only [h1, show ¬ i - 32 < 32 by omega, show ¬ i - 32 - 32 < 32 by omega,
      show i - 32 - 32 - 32 < 32 by omega, ite_false, decide_true, Bool.true_and] <;>
      exact congrArg _ (by omega)

/-- Two values are equal if their doublewords are. -/
theorem ext_dword {x y : BitVec 128} (h0 : dword x 0 = dword y 0) (h1 : dword x 1 = dword y 1)
    (h2 : dword x 2 = dword y 2) (h3 : dword x 3 = dword y 3) : x = y := by
  rw [← ofDwords_dword x, ← ofDwords_dword y, h0, h1, h2, h3]

@[simp] theorem eval_movdqa (a b : BitVec 128) : XBinOp.eval .movdqa a b = b := rfl

theorem eval_sha256msg2 (a b : BitVec 128) : XBinOp.eval .sha256msg2 a b = sha256Msg2 a b := rfl

theorem punpcklqdq_eq (a b : BitVec 128) :
    XBinOp.eval .punpcklqdq a b = ofDwords (dword a 0) (dword a 1) (dword b 0) (dword b 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, qword, getLsbD_ofDwords, getLsbD_dword, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  by_cases h1 : i < 32
  · simp only [h1, ite_true, decide_true, Bool.true_and, show i < 64 by omega] <;> exact congrArg _ (by omega)
  by_cases h2 : i < 64
  · simp only [h1, show i - 32 < 32 by omega, ite_true, ite_false, decide_true,
      Bool.true_and, h2] <;> exact congrArg _ (by omega)
  by_cases h3 : i < 96
  · simp only [h1, show ¬ i - 32 < 32 by omega, show i - 32 - 32 < 32 by omega, ite_true, ite_false,
      decide_true, Bool.true_and, h2, show i - 64 < 64 by omega] <;> exact congrArg _ (by omega)
  · simp only [h1, show ¬ i - 32 < 32 by omega, show ¬ i - 32 - 32 < 32 by omega,
      show i - 32 - 32 - 32 < 32 by omega, ite_false, decide_true, Bool.true_and, h2, show i - 64 < 64 by omega] <;>
      exact congrArg _ (by omega)

theorem punpckhqdq_eq (a b : BitVec 128) :
    XBinOp.eval .punpckhqdq a b = ofDwords (dword a 2) (dword a 3) (dword b 2) (dword b 3) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, qword, getLsbD_ofDwords, getLsbD_dword, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  by_cases h1 : i < 32
  · simp only [h1, ite_true, decide_true, Bool.true_and, show i < 64 by omega] <;> exact congrArg _ (by omega)
  by_cases h2 : i < 64
  · simp only [h1, show i - 32 < 32 by omega, ite_true, ite_false, decide_true,
      Bool.true_and, h2] <;> exact congrArg _ (by omega)
  by_cases h3 : i < 96
  · simp only [h1, show ¬ i - 32 < 32 by omega, show i - 32 - 32 < 32 by omega, ite_true, ite_false,
      decide_true, Bool.true_and, h2, show i - 64 < 64 by omega] <;> exact congrArg _ (by omega)
  · simp only [h1, show ¬ i - 32 < 32 by omega, show ¬ i - 32 - 32 < 32 by omega,
      show i - 32 - 32 - 32 < 32 by omega, ite_false, decide_true, Bool.true_and, h2, show i - 64 < 64 by omega] <;>
      exact congrArg _ (by omega)

theorem shufDwords_b1 (a : BitVec 128) :
    shufDwords a 0xb1 = ofDwords (dword a 1) (dword a 0) (dword a 3) (dword a 2) := rfl

theorem shufDwords_0e (a : BitVec 128) :
    shufDwords a 0x0e = ofDwords (dword a 2) (dword a 3) (dword a 0) (dword a 0) := rfl

theorem alignRight_4 (a b : BitVec 128) :
    alignRight a b 4 = ofDwords (dword b 1) (dword b 2) (dword b 3) (dword a 0) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e : (4 : BitVec 8).toNat * 8 = 32 := rfl
  simp only [alignRight, e, getLsbD_ofDwords, getLsbD_dword, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, decide_eq_true hi, Bool.true_and,
    Nat.zero_add]
  by_cases h1 : i < 32
  · simp only [h1, ite_true, decide_true, Bool.true_and, show 32 + i < 128 by omega] <;> exact congrArg _ (by omega)
  by_cases h2 : i < 64
  · simp only [h1, show i - 32 < 32 by omega, ite_true, ite_false, decide_true,
      Bool.true_and, show 32 + i < 128 by omega] <;> exact congrArg _ (by omega)
  by_cases h3 : i < 96
  · simp only [h1, show ¬ i - 32 < 32 by omega, show i - 32 - 32 < 32 by omega, ite_true, ite_false,
      decide_true, Bool.true_and, show 32 + i < 128 by omega] <;> exact congrArg _ (by omega)
  · simp only [h1, show ¬ i - 32 < 32 by omega, show ¬ i - 32 - 32 < 32 by omega,
      show i - 32 - 32 - 32 < 32 by omega, ite_false, decide_true, Bool.true_and, show ¬ 32 + i < 128 by omega] <;>
      exact congrArg _ (by omega)

theorem movq_const (c : BitVec 128) :
    XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ c.extractLsb' 0 64)
      ((0 : BitVec 64) ++ c.extractLsb' 64 64) = c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 64 ∨ 64 ≤ i) with h | h <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and] <;>
  exact congrArg _ (by omega)


/-- Bit `r` of block `k` of `x ++ y`, blocks being `n` bits wide. -/
theorem getLsbD_append_block {w n : Nat} (x : BitVec w) (y : BitVec n) (k : Nat) {r : Nat} (hr : r < n) :
    (x ++ y).getLsbD (n * k + r) = if k = 0 then y.getLsbD r else x.getLsbD (n * (k - 1) + r) := by
  rw [BitVec.getLsbD_append]
  by_cases hk : k = 0
  · subst hk; simp [hr]
  · have h : n ≤ n * k := Nat.le_mul_of_pos_right n (by omega)
    simp only [hk, show ¬ n * k + r < n by omega, ↓reduceIte]
    exact congrArg _ (by rw [Nat.mul_sub_one, Nat.sub_add_comm h])

theorem getLsbD_ofBytes (f : Nat → BitVec 8) {k r : Nat} (hk : k < 16) (hr : r < 8) :
    (ofBytes f).getLsbD (8 * k + r) = (f k).getLsbD r := by
  simp only [ofBytes, getLsbD_append_block _ _ _ hr]
  match k, hk with
  | 0, _ => ?_
  | 1, _ => ?_
  | 2, _ => ?_
  | 3, _ => ?_
  | 4, _ => ?_
  | 5, _ => ?_
  | 6, _ => ?_
  | 7, _ => ?_
  | 8, _ => ?_
  | 9, _ => ?_
  | 10, _ => ?_
  | 11, _ => ?_
  | 12, _ => ?_
  | 13, _ => ?_
  | 14, _ => ?_
  | 15, _ => ?_
  | _ + 16, h => exact absurd h (by omega)
  all_goals
    simp only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add]

theorem pshufb_bswap_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a 0x0c0d0e0f08090a0b0405060700010203#128 =
      ofBytes fun j => byte a (4 * (j / 4) + 3 - j % 4) := by
  simp only [XBinOp.eval, ofBytes]
  rfl
theorem getLsbD_bswap (x : BitVec 32) (i : Nat) :
    (bswap x).getLsbD i = if i < 8 then x.getLsbD (24 + i) else if i - 8 < 8 then x.getLsbD (16 + (i - 8))
      else if i - 8 - 8 < 8 then x.getLsbD (8 + (i - 8 - 8)) else (decide (i - 8 - 8 - 8 < 8) && x.getLsbD (i - 8 - 8 - 8)) := by
  simp only [bswap, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i) with h | h | h | h <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and, Nat.zero_add]

theorem getLsbD_ofDwords_block (a b c d : BitVec 32) {q s : Nat} (hq : q < 4) (hs : s < 32) :
    (ofDwords a b c d).getLsbD (32 * q + s) =
      if q = 0 then a.getLsbD s else if q = 1 then b.getLsbD s else if q = 2 then c.getLsbD s
      else d.getLsbD s := by
  simp only [ofDwords, getLsbD_append_block _ _ _ hs]
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with h | h | h | h <;> subst h <;>
  simp only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add]

theorem getLsbD_bswap_block (x : BitVec 32) {j r : Nat} (hj : j < 4) (hr : r < 8) :
    (bswap x).getLsbD (8 * j + r) =
      if j = 0 then x.getLsbD (24 + r) else if j = 1 then x.getLsbD (16 + r)
      else if j = 2 then x.getLsbD (8 + r) else x.getLsbD r := by
  simp only [bswap, getLsbD_append_block _ _ _ hr]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with h | h | h | h <;> subst h <;>
  simp (disch := omega) only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add,
    BitVec.getLsbD_extractLsb', decide_eq_true, Bool.true_and]

theorem pshufb_bswap (a : BitVec 128) :
    XBinOp.eval .pshufb a 0x0c0d0e0f08090a0b0405060700010203#128 =
      ofDwords (bswap (dword a 0)) (bswap (dword a 1)) (bswap (dword a 2)) (bswap (dword a 3)) := by
  rw [pshufb_bswap_bytes]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨k, r, hk, hr, rfl⟩ : ∃ k r, k < 16 ∧ r < 8 ∧ i = 8 * k + r :=
    ⟨i / 8, i % 8, by omega, by omega, by omega⟩
  rw [getLsbD_ofBytes _ hk hr, show 8 * k + r = 32 * (k / 4) + (8 * (k % 4) + r) by omega,
    getLsbD_ofDwords_block _ _ _ _ (by omega) (by omega)]
  simp only [getLsbD_bswap_block _ (Nat.mod_lt k (by decide : 4 > 0)) hr]
  match k, hk with
  | 0, _ => ?_
  | 1, _ => ?_
  | 2, _ => ?_
  | 3, _ => ?_
  | 4, _ => ?_
  | 5, _ => ?_
  | 6, _ => ?_
  | 7, _ => ?_
  | 8, _ => ?_
  | 9, _ => ?_
  | 10, _ => ?_
  | 11, _ => ?_
  | 12, _ => ?_
  | 13, _ => ?_
  | 14, _ => ?_
  | 15, _ => ?_
  | _ + 16, h => exact absurd h (by omega)
  all_goals
    simp (disch := omega) only [↓reduceIte, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff,
      Nat.reduceAdd, Nat.reduceMul, ← Nat.add_assoc, byte, dword, BitVec.getLsbD_extractLsb',
      decide_eq_true, Bool.true_and]

theorem getLsbD_read (m : Mem) (a : Addr) {n i : Nat} (hi : i < 8 * n) :
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8) := by
  induction n generalizing a i with
  | zero => omega
  | succ n ih =>
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases h : i < 8
    · simp only [h, ite_true, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · simp only [h, ite_false]
      refine (ih (a + 1) (by omega)).trans ?_
      rw [show a + BitVec.ofNat 64 (i / 8) = a + 1 + BitVec.ofNat 64 ((i - 8) / 8) by
        rw [show i / 8 = (i - 8) / 8 + 1 by omega, Offset.add_ofNat_succ]]
      exact congrArg _ (by omega)

theorem dword_readW (m : Mem) (a : Addr) {j : Nat} (hj : j < 4) :
    dword (m.readW a 128) j = m.readW (a + BitVec.ofNat 64 (4 * j)) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [dword, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth]
  by_cases h : i < 32
  · simp only [h, decide_true, Bool.true_and]
    rw [getLsbD_read _ _ (by omega), getLsbD_read _ _ (by omega)]
    rw [show a + BitVec.ofNat 64 ((32 * j + i) / 8) = a + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 (i / 8) by
      rw [show (32 * j + i) / 8 = 4 * j + i / 8 by omega, BitVec.ofNat_add, BitVec.add_assoc]]
    rw [decide_eq_true (by omega), Bool.true_and]; exact congrArg _ (by omega)
  · simp [h]

theorem readW_writeW128 (m : Mem) (a : Addr) (v : BitVec 128) {j : Nat} (hj : j < 4) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (4 * j)) 32 = dword v j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [dword, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_read _ _ (by omega)]
  simp only [Mem.writeW, Mem.write]
  rw [show a + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 (i / 8) - a = BitVec.ofNat 64 (4 * j + i / 8) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left]]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [show 4 * j + i / 8 < 128 / 8 by omega, ite_true, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  rw [decide_eq_true (by omega), decide_eq_true (by omega), Bool.true_and, Bool.true_and]
  exact congrArg _ (by omega)
end VG.X86
