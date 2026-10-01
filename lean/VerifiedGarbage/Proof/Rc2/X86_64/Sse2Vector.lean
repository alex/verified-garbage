import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Exec

/-! # Word-wise SSE2 lookup invariants -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64

theorem word_por (a b : BitVec 128) (i : Nat) :
    word (a ||| b) i = word a i ||| word b i := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [getLsbD_word, BitVec.getLsbD_or, decide_eq_true hj, Bool.true_and]

def broadcast (x : Byte) : BitVec 128 := ofWords fun _ => x.setWidth 16

theorem broadcast_word (x : Byte) (i : Nat) (hi : i < 8) :
    word (shufDwords (XBinOp.eval .punpcklwd
      (0#64 ++ x.setWidth 64) (0#64 ++ x.setWidth 64)) 0) i = x.setWidth 16 := by
  have hd : dword (XBinOp.eval .punpcklwd
      (0#64 ++ x.setWidth 64) (0#64 ++ x.setWidth 64)) 0 =
      x.setWidth 16 ++ x.setWidth 16 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [dword, XBinOp.eval, ofWords, word, BitVec.getLsbD_extractLsb',
      Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff,
      Nat.zero_add, ite_true, ite_false, decide_eq_true hj, Bool.true_and]
    repeat rw [BitVec.getLsbD_append]
    by_cases h : j < 16 <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, BitVec.getLsbD_extractLsb',
        Nat.zero_add, decide_eq_true, Bool.true_and]
    all_goals rw [BitVec.getLsbD_append]
    all_goals simp (disch := omega) only [ite_eq_left, BitVec.getLsbD_setWidth,
      decide_eq_true, Bool.true_and]
  rw [shufDwords]
  change word (ofDwords
    (dword _ 0) (dword _ 0) (dword _ 0) (dword _ 0)) i = _
  rw [hd]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [word_eq_dword _ hi] <;>
    simp (disch := decide) only [Nat.reduceDiv, Nat.reduceMod,
      dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
      Nat.reduceMul, Nat.reduceSub, BitVec.extractLsb'_append_eq_of_add_le,
      BitVec.extractLsb'_append_eq_of_le, BitVec.extractLsb'_eq_self]


def acc (f : Nat → BitVec 16) (x n : Nat) : BitVec 128 :=
  ofWords fun j => if x < 8 * n ∧ x % 8 = j then f x else 0#16

theorem acc_zero (f : Nat → BitVec 16) (x : Nat) : acc f x 0 = 0#128 := by
  apply ext_word
  intro j hj
  rw [acc, word_ofWords _ hj]
  simp [word]

theorem indices_next (n : Nat) :
    XBinOp.eval .paddw (Impl.Rc2.X86_64.Sse2.indices n)
      Impl.Rc2.X86_64.Sse2.eights = Impl.Rc2.X86_64.Sse2.indices (n + 1) := by
  apply ext_word
  intro j hj
  rw [word_paddw _ _ hj]
  simp only [Impl.Rc2.X86_64.Sse2.indices, Impl.Rc2.X86_64.Sse2.eights, word_ofWords _ hj]
  change BitVec.ofNat 16 (8 * n + j) + BitVec.ofNat 16 8 = _
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem acc_step (f : Nat → BitVec 16) (x : Byte) (n : Nat) (hn : n < 32)
    (v : BitVec 128) (hv : ∀ j < 8, word v j = f (8 * n + j)) :
    acc f x.toNat n ||| selectValue (broadcast x)
      (Impl.Rc2.X86_64.Sse2.indices n) Impl.Rc2.X86_64.Sse2.ones v =
    acc f x.toNat (n + 1) := by
  apply ext_word
  intro j hj
  rw [word_por, selectValue_word _ _ _ x (BitVec.ofNat 8 (8 * n + j)) j hj
    (word_ofWords _ hj) (by
      rw [Impl.Rc2.X86_64.Sse2.indices, word_ofWords _ hj]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega)]
  simp only [acc, word_ofWords _ hj, hv j hj]
  have he : (x = BitVec.ofNat 8 (8 * n + j)) ↔ x.toNat = 8 * n + j := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases h : x.toNat = 8 * n + j
  · rw [ite_eq_left (he.mpr h), ite_eq_right (by omega), ite_eq_left (by omega), h]
    exact BitVec.zero_or
  · rw [ite_eq_right (mt he.mp h)]
    change (if x.toNat < 8 * n ∧ x.toNat % 8 = j then f x.toNat else 0#16) ||| 0#16 = _
    rw [BitVec.or_zero]
    have heq : (x.toNat < 8 * n ∧ x.toNat % 8 = j) ↔
        (x.toNat < 8 * (n + 1) ∧ x.toNat % 8 = j) := by omega
    simp only [heq]

def reduceValue (v : BitVec 128) : BitVec 128 :=
  let a := v ||| (v >>> 64)
  let b := a ||| (a >>> 32)
  b ||| (b >>> 16)

theorem reduceValue_word (v : BitVec 128) :
    word (reduceValue v) 0 =
      word v 0 ||| word v 1 ||| word v 2 ||| word v 3 |||
      word v 4 ||| word v 5 ||| word v 6 ||| word v 7 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [reduceValue, getLsbD_word, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    decide_eq_true hj, Bool.true_and, Nat.mul_zero, Nat.zero_add]
  simp only [Nat.reduceMul]
  simp only [Nat.add_assoc, Nat.add_comm, Bool.or_comm, Bool.or_left_comm]

theorem reduce_acc (f : Nat → BitVec 16) (x n : Nat) :
    word (reduceValue (acc f x n)) 0 = if x < 8 * n then f x else 0#16 := by
  rw [reduceValue_word]
  simp only [acc, word_ofWords _ (by decide : 0 < 8), word_ofWords _ (by decide : 1 < 8),
    word_ofWords _ (by decide : 2 < 8), word_ofWords _ (by decide : 3 < 8),
    word_ofWords _ (by decide : 4 < 8), word_ofWords _ (by decide : 5 < 8),
    word_ofWords _ (by decide : 6 < 8), word_ofWords _ (by decide : 7 < 8)]
  by_cases h : x < 8 * n
  · rw [ite_eq_left h]
    rcases (by omega : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨
      x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7) with
      hm | hm | hm | hm | hm | hm | hm | hm <;>
      simp only [h, hm, Nat.reduceEqDiff, ite_true, ite_false, true_and, and_false,
        BitVec.or_zero, BitVec.zero_or]
  · simp only [h, false_and, ite_false, BitVec.or_zero]


end VG.Proof.Rc2.X86_64.Sse2
