import VerifiedGarbage.Proof.Framework.X86_64.Sse

/-!
# x86-64: SSE values as words

Untrusted: everything here is checked by Lean. The SSE instructions on
16-bit words, stated on the words of their operands (`word`, `ofWords`), and
128-bit loads and stores as eight 16-bit words.
-/

namespace VG.X86_64

theorem getLsbD_word (x : BitVec 128) (k i : Nat) :
    (word x k).getLsbD i = (decide (i < 16) && x.getLsbD (16 * k + i)) := by
  simp only [word, BitVec.getLsbD_extractLsb']

theorem getLsbD_ofWords (f : Nat → BitVec 16) {k r : Nat} (hk : k < 8) (hr : r < 16) :
    (ofWords f).getLsbD (16 * k + r) = (f k).getLsbD r := by
  unfold ofWords
  simp only [BitVec.getLsbD_append]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  (repeat' split) <;> first | (exfalso; omega) | (congr 1; omega)

@[simp] theorem word_ofWords (f : Nat → BitVec 16) {i : Nat} (hi : i < 8) : word (ofWords f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [getLsbD_word, decide_eq_true hj, Bool.true_and, getLsbD_ofWords f hi hj]

/-- Two values are equal if their words are. -/
theorem ext_word {x y : BitVec 128} (h : ∀ i < 8, word x i = word y i) : x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have := congrArg (fun w : BitVec 16 => w.getLsbD (j % 16)) (h (j / 16) (by omega))
  simp only [getLsbD_word, show j % 16 < 16 by omega, decide_true, Bool.true_and,
    show 16 * (j / 16) + j % 16 = j by omega] at this
  exact this

theorem ofWords_word (x : BitVec 128) : ofWords (word x) = x :=
  ext_word fun _ hi => word_ofWords _ hi

/-- The words of a doubleword. -/
theorem word_dword (x : BitVec 128) {k : Nat} (_hk : k < 4) (e : Nat) (he : e < 2) :
    word x (2 * k + e) = (dword x k).extractLsb' (16 * e) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [getLsbD_word, dword, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and,
    decide_eq_true (show 16 * e + j < 32 by omega)]
  congr 1; omega

/-- A word is the word of its doubleword. -/
theorem word_eq_dword (x : BitVec 128) {i : Nat} (hi : i < 8) :
    word x i = (dword x (i / 2)).extractLsb' (16 * (i % 2)) 16 := by
  have := word_dword x (k := i / 2) (by omega) (i % 2) (by omega)
  rwa [show 2 * (i / 2) + i % 2 = i by omega] at this

/-! ## Loads and stores -/

theorem word_readW (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    word (m.readW a 128) j = m.readW (a + BitVec.ofNat 64 (2 * j)) 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [word, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  rw [getLsbD_read _ _ (by omega), getLsbD_read _ _ (by omega)]
  rw [show a + BitVec.ofNat 64 ((16 * j + i) / 8) = a + BitVec.ofNat 64 (2 * j) + BitVec.ofNat 64 (i / 8) by
    rw [show (16 * j + i) / 8 = 2 * j + i / 8 by omega, BitVec.ofNat_add, BitVec.add_assoc]]
  simp only [decide_eq_true (show 16 * j + i < 128 by omega), Bool.true_and]
  exact congrArg _ (by omega)

theorem readW_writeW128_16 (m : Mem) (a : Addr) (v : BitVec 128) {j : Nat} (hj : j < 8) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (2 * j)) 16 = word v j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [word, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_read _ _ (by omega)]
  simp only [Mem.writeW, Mem.write]
  rw [show a + BitVec.ofNat 64 (2 * j) + BitVec.ofNat 64 (i / 8) - a = BitVec.ofNat 64 (2 * j + i / 8) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left]]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [show 2 * j + i / 8 < 128 / 8 by omega, ite_true, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth]
  rw [decide_eq_true (by omega), decide_eq_true (by omega), Bool.true_and, Bool.true_and]
  exact congrArg _ (by omega)

/-! ## The word instructions -/

section
variable (a b : BitVec 128) {i : Nat}

theorem word_paddw (hi : i < 8) : word (XBinOp.eval .paddw a b) i = word a i + word b i := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi
theorem word_psubw (hi : i < 8) : word (XBinOp.eval .psubw a b) i = word a i - word b i := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi
theorem word_pmullw (hi : i < 8) :
    word (XBinOp.eval .pmullw a b) i = (mulWordsSigned (word a i) (word b i)).extractLsb' 0 16 := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi
theorem word_pmulhw (hi : i < 8) :
    word (XBinOp.eval .pmulhw a b) i = (mulWordsSigned (word a i) (word b i)).extractLsb' 16 16 := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi
theorem word_punpcklwd (hi : i < 8) :
    word (XBinOp.eval .punpcklwd a b) i = if i % 2 = 0 then word a (i / 2) else word b (i / 2) := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi
theorem word_punpckhwd (hi : i < 8) :
    word (XBinOp.eval .punpckhwd a b) i = if i % 2 = 0 then word a (4 + i / 2) else word b (4 + i / 2) := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi
theorem word_packssdw (hi : i < 8) :
    word (XBinOp.eval .packssdw a b) i =
      if i < 4 then satSignedWord (dword a i) else satSignedWord (dword b (i - 4)) := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi

theorem word_psraw (n : BitVec 8) (hi : i < 8) :
    word (XShiftOp.eval .psraw a n) i = (word a i).sshiftRight (min n.toNat 16) := by
  simp only [XShiftOp.eval]; exact word_ofWords _ hi

theorem word_pand : word (XBinOp.eval .pand a b) i = word a i &&& word b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [XBinOp.eval, getLsbD_word, BitVec.getLsbD_and, decide_eq_true hj, Bool.true_and]

theorem word_pxor : word (XBinOp.eval .pxor a b) i = word a i ^^^ word b i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [XBinOp.eval, getLsbD_word, BitVec.getLsbD_xor, decide_eq_true hj, Bool.true_and]

theorem word_movdqa : word (XBinOp.eval .movdqa a b) i = word b i := rfl

theorem word_punpcklqdq (hi : i < 8) :
    word (XBinOp.eval .punpcklqdq a b) i = if i < 4 then word a i else word b (i - 4) := by
  rw [punpcklqdq_eq, word_eq_dword _ hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceLT, Nat.reduceSub, ite_true, ite_false,
    dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, word_eq_dword]

theorem word_punpckhqdq (hi : i < 8) :
    word (XBinOp.eval .punpckhqdq a b) i = if i < 4 then word a (4 + i) else word b i := by
  rw [punpckhqdq_eq, word_eq_dword _ hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [Nat.reduceDiv, Nat.reduceMod, Nat.reduceLT, Nat.reduceAdd, ite_true, ite_false,
    dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, word_eq_dword]

end

end VG.X86_64
