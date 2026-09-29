import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Spec
import VerifiedGarbage.Impl.Sha256.X86_64.Avx2
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Lit

/-!
# SHA-256 with AVX2 on x86-64: the message schedule of one lane

Untrusted: everything here is checked by Lean. Each 256-bit instruction of
the schedule acts on the two 128-bit lanes alike, so it is proved once, on
one lane (`xupd`): the next four words of a block's schedule from its
previous sixteen.
-/

namespace VG.Proof.Sha256.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Avx2
open VG.Spec.Sha256 (Word Block W ssig0 ssig1)
open VG.Proof.Sha256.X86_64.ShaNi (quad W_ge')

/-! ## The instructions, on doublewords -/

theorem dword_xor (a b : BitVec 128) (k : Nat) : dword (a ^^^ b) k = dword a k ^^^ dword b k := by
  ext i hi
  simp only [dword, BitVec.getElem_extractLsb', BitVec.getLsbD_xor, BitVec.getElem_xor]

theorem xor_ofDwords (a b : BitVec 128) :
    a ^^^ b = ofDwords (dword a 0 ^^^ dword b 0) (dword a 1 ^^^ dword b 1) (dword a 2 ^^^ dword b 2)
      (dword a 3 ^^^ dword b 3) := by
  apply ext_dword <;> simp only [dword_xor, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3]

theorem psrld_eq (a : BitVec 128) (n : BitVec 8) (h : n.toNat < 32) :
    XShiftOp.eval .psrld a n =
      ofDwords (dword a 0 >>> n.toNat) (dword a 1 >>> n.toNat) (dword a 2 >>> n.toNat)
        (dword a 3 >>> n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 31 < n.toNat by omega, ite_false]

theorem pslld_eq (a : BitVec 128) (n : BitVec 8) (h : n.toNat < 32) :
    XShiftOp.eval .pslld a n =
      ofDwords (dword a 0 <<< n.toNat) (dword a 1 <<< n.toNat) (dword a 2 <<< n.toNat)
        (dword a 3 <<< n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 31 < n.toNat by omega, ite_false]

theorem qword_ofDwords_0 (a c b d : BitVec 32) : qword (ofDwords a c b d) 0 = c ++ a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, ofDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.mul_zero,
    Nat.zero_add, decide_eq_true hi, Bool.true_and]
  by_cases h : i < 32
  · simp only [h, ite_true]
  · simp only [h, ite_false, show i - 32 < 32 by omega, ite_true]

theorem qword_ofDwords_1 (a c b d : BitVec 32) : qword (ofDwords a c b d) 1 = d ++ b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, ofDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.mul_one,
    decide_eq_true hi, Bool.true_and, show ¬ 64 + i < 32 by omega, show ¬ 64 + i - 32 < 32 by omega,
    ite_false]
  by_cases h : i < 32
  · simp only [h, ite_true, show 64 + i - 32 - 32 = i by omega]
  · simp only [h, show ¬ 64 + i - 32 - 32 < 32 by omega, ite_false,
      show 64 + i - 32 - 32 - 32 = i - 32 by omega]

theorem shr_append (c a : BitVec 32) {m : Nat} (h : m < 32) :
    (c ++ a : BitVec 64) >>> m = (c >>> m) ++ (a >>> m ||| c <<< (32 - m)) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  by_cases h1 : i < 32
  · by_cases h2 : m + i < 32
    · simp only [h1, h2, ite_true, decide_true, show i < 32 - m by omega, Bool.not_true, Bool.true_and,
        Bool.false_and, Bool.or_false]
    · simp only [h1, h2, ite_true, ite_false, decide_true, show ¬ i < 32 - m by omega, decide_false,
        Bool.not_false, Bool.true_and, BitVec.getLsbD_of_ge a (m + i) (by omega), Bool.false_or,
        show i - (32 - m) = m + i - 32 by omega]
  · simp only [h1, show ¬ m + i < 32 by omega, ite_false, show m + (i - 32) = m + i - 32 by omega]

theorem append_pairs (p q r s : BitVec 32) : (p ++ q) ++ (r ++ s) = ofDwords s r q p := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ofDwords, BitVec.getLsbD_append]
  simp only [Nat.reduceAdd, Nat.sub_sub]
  by_cases h1 : i < 32
  · simp only [h1, show i < 64 by omega, ite_true]
  by_cases h2 : i < 64
  · simp only [h1, h2, show i - 32 < 32 by omega, ite_true, ite_false]
  by_cases h3 : i < 96
  · simp only [h1, h2, show ¬ i - 32 < 32 by omega, show i - 64 < 32 by omega, ite_true, ite_false]
  · simp only [h1, h2, show ¬ i - 32 < 32 by omega, show ¬ i - 64 < 32 by omega, ite_false]

/-- A quadword shift right, on doublewords: the high doubleword of each
quadword shifts into the low one. -/
theorem psrlq_eq (a c b d : BitVec 32) (n : BitVec 8) (h : n.toNat < 32) :
    XShiftOp.eval .psrlq (ofDwords a c b d) n =
      ofDwords (a >>> n.toNat ||| c <<< (32 - n.toNat)) (c >>> n.toNat)
        (b >>> n.toNat ||| d <<< (32 - n.toNat)) (d >>> n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false, qword_ofDwords_0,
    qword_ofDwords_1, shr_append _ _ h, append_pairs]

theorem pshufb_BA_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a maskBA =
      ofBytes fun j => if j < 4 then byte a j else if j < 8 then byte a (j + 4) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem pshufb_DC_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a maskDC =
      ofBytes fun j => if j < 8 then 0 else if j < 12 then byte a (j - 8) else byte a (j - 4) := by
  simp only [XBinOp.eval, ofBytes]
  rfl

/-- `vpshufb` with `maskBA`: doublewords 0 and 2 into 0 and 1, zeros above. -/
theorem pshufb_BA (a : BitVec 128) :
    XBinOp.eval .pshufb a maskBA = ofDwords (dword a 0) (dword a 2) 0 0 := by
  rw [pshufb_BA_bytes]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨k, r, hk, hr, rfl⟩ : ∃ k r, k < 16 ∧ r < 8 ∧ i = 8 * k + r :=
    ⟨i / 8, i % 8, by omega, by omega, by omega⟩
  rw [getLsbD_ofBytes _ hk hr, show 8 * k + r = 32 * (k / 4) + (8 * (k % 4) + r) by omega,
    getLsbD_ofDwords_block _ _ _ _ (by omega) (by omega)]
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
  simp (disch := omega) only [↓reduceIte, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, ← Nat.add_assoc, byte, dword, BitVec.getLsbD_extractLsb',
    decide_eq_true, Bool.true_and] <;>
  simp

/-- `vpshufb` with `maskDC`: doublewords 0 and 2 into 2 and 3, zeros below. -/
theorem pshufb_DC (a : BitVec 128) :
    XBinOp.eval .pshufb a maskDC = ofDwords 0 0 (dword a 0) (dword a 2) := by
  rw [pshufb_DC_bytes]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨k, r, hk, hr, rfl⟩ : ∃ k r, k < 16 ∧ r < 8 ∧ i = 8 * k + r :=
    ⟨i / 8, i % 8, by omega, by omega, by omega⟩
  rw [getLsbD_ofBytes _ hk hr, show 8 * k + r = 32 * (k / 4) + (8 * (k % 4) + r) by omega,
    getLsbD_ofDwords_block _ _ _ _ (by omega) (by omega)]
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
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, ← Nat.add_assoc, byte, dword, BitVec.getLsbD_extractLsb',
    decide_eq_true, Bool.true_and] <;>
  simp

theorem shufDwords_fa (a : BitVec 128) :
    shufDwords a 0xfa = ofDwords (dword a 2) (dword a 2) (dword a 3) (dword a 3) := rfl

theorem shufDwords_50 (a : BitVec 128) :
    shufDwords a 0x50 = ofDwords (dword a 0) (dword a 0) (dword a 1) (dword a 1) := rfl

theorem paddd_eq (a b : BitVec 128) :
    XBinOp.eval .paddd a b = ofDwords (dword a 0 + dword b 0) (dword a 1 + dword b 1)
      (dword a 2 + dword b 2) (dword a 3 + dword b 3) := rfl

theorem pxor_eq (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

/-! ## One lane of `schedule` -/

/-- What `schedule` computes in one lane, from the lane's four message
registers `x₀ … x₃` (oldest first), as its instructions do. -/
def xupd (x₀ x₁ x₂ x₃ : BitVec 128) : BitVec 128 :=
  let t₀ := alignRight x₁ x₀ 4
  let t₃ := alignRight x₃ x₂ 4
  let t₂ := XShiftOp.eval .psrld t₀ 7
  let y := XBinOp.eval .paddd x₀ t₃
  let t₃ := XShiftOp.eval .psrld t₀ 3
  let t₁ := XShiftOp.eval .pslld t₀ 14
  let t₀ := XBinOp.eval .pxor t₃ t₂
  let t₃ := shufDwords x₃ 0xfa
  let t₂ := XShiftOp.eval .psrld t₂ 11
  let t₀ := XBinOp.eval .pxor t₀ t₁
  let t₁ := XShiftOp.eval .pslld t₁ 11
  let t₀ := XBinOp.eval .pxor t₀ t₂
  let t₂ := XShiftOp.eval .psrld t₃ 10
  let t₀ := XBinOp.eval .pxor t₀ t₁
  let t₃ := XShiftOp.eval .psrlq t₃ 17
  let y := XBinOp.eval .paddd y t₀
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let t₃ := XShiftOp.eval .psrlq t₃ 2
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let t₂ := XBinOp.eval .pshufb t₂ maskBA
  let y := XBinOp.eval .paddd y t₂
  let t₃ := shufDwords y 0x50
  let t₂ := XShiftOp.eval .psrld t₃ 10
  let t₃ := XShiftOp.eval .psrlq t₃ 17
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let t₃ := XShiftOp.eval .psrlq t₃ 2
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let t₂ := XBinOp.eval .pshufb t₂ maskDC
  XBinOp.eval .paddd y t₂

/-- `σ₀`, as `schedule` computes it: shifts by 3, 7, 14, 18 and 25. -/
theorem ssig0_shifts (x : Word) :
    (x >>> 3 ^^^ x >>> 7 ^^^ x <<< 14 ^^^ x >>> 7 >>> 11 ^^^ x <<< 14 <<< 11) = ssig0 x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ssig0, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_rotateRight, Nat.reduceMod, Nat.reduceSub, decide_eq_true hi, Bool.true_and,
    show 7 + (11 + i) = 18 + i by omega]
  by_cases h14 : i < 14
  · simp only [h14, show i < 25 by omega, show i - 11 < 32 by omega, show i - 11 < 14 by omega,
      decide_true, Bool.not_true, Bool.false_and, Bool.and_false, Bool.xor_false, ite_true]
    simp only [Bool.xor_comm, Bool.xor_assoc]
  have h18 : x.getLsbD (18 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
  by_cases h25 : i < 25
  · simp only [h14, h25, h18, show i - 11 < 32 by omega, show i - 11 < 14 by omega, decide_true,
      decide_false, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_false,
      Bool.xor_false, ite_true, ite_false]
    simp only [Bool.xor_comm, Bool.xor_assoc]
  · simp only [h14, h25, h18, BitVec.getLsbD_of_ge x (7 + i) (by omega),
      show ¬ i < 11 by omega, show i - 11 < 32 by omega, show ¬ i - 11 < 14 by omega, decide_true,
      decide_false, Bool.not_false, Bool.true_and,
      Bool.xor_false, ite_false, Nat.sub_sub, Nat.reduceAdd]
    simp only [Bool.xor_comm, Bool.xor_assoc]


/-- `σ₁`, as `schedule` computes it: shifts of the word doubled into a quadword. -/
theorem ssig1_shifts (x : Word) :
    (x >>> 10 ^^^ (x >>> 17 ||| x <<< 15) ^^^ ((x >>> 17 ||| x <<< 15) >>> 2 ||| x >>> 17 <<< 30)) =
      ssig1 x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ssig1, BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_rotateRight, Nat.reduceMod, Nat.reduceSub, decide_eq_true hi, Bool.true_and,
    show 17 + (2 + i) = 19 + i by omega]
  by_cases h13 : i < 13
  · simp only [h13, show i < 15 by omega, show 2 + i < 15 by omega, show i < 30 by omega, decide_true,
      Bool.not_true, Bool.false_and, Bool.and_false, Bool.or_false, ite_true]
    simp only [Bool.xor_comm, Bool.xor_assoc]
  have h19 : x.getLsbD (19 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
  by_cases h15 : i < 15
  · simp only [h13, h15, h19, show ¬ 2 + i < 15 by omega, show 2 + i < 32 by omega,
      show i < 30 by omega, show 2 + i - 15 = i - 13 by omega, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false,
      Bool.false_or, ite_true, ite_false]
    simp only [Bool.xor_comm, Bool.xor_left_comm]
  have h17 : x.getLsbD (17 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
  by_cases h30 : i < 30
  · simp only [h13, h15, h19, h17, h30, show ¬ 2 + i < 15 by omega, show 2 + i < 32 by omega,
      show 2 + i - 15 = i - 13 by omega, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false,
      Bool.false_or, ite_false]
    simp only [Bool.xor_comm, Bool.xor_left_comm]
  · simp only [h13, h15, h19, h17, h30, show ¬ 2 + i < 32 by omega, show 17 + (i - 30) = i - 13 by omega,
      BitVec.getLsbD_of_ge x (10 + i) (by omega), decide_false,
      Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false,
      Bool.false_or, Bool.false_xor, Bool.xor_false, ite_false]

theorem word_add_zero (x : Word) : x + 0 = x := BitVec.add_zero x

/-- `schedule`, on one lane: from `W₄ᵢ₋₁₆ … W₄ᵢ₋₁` (`w₀ … w₁₅`), the next
four words. -/
theorem xupd_eq (w₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ w₁₄ w₁₅ : Word) :
    xupd (ofDwords w₀ w₁ w₂ w₃) (ofDwords w₄ w₅ w₆ w₇) (ofDwords w₈ w₉ w₁₀ w₁₁)
      (ofDwords w₁₂ w₁₃ w₁₄ w₁₅) =
      ofDwords (w₀ + w₉ + ssig0 w₁ + ssig1 w₁₄) (w₁ + w₁₀ + ssig0 w₂ + ssig1 w₁₅)
        (w₂ + w₁₁ + ssig0 w₃ + ssig1 (w₀ + w₉ + ssig0 w₁ + ssig1 w₁₄))
        (w₃ + w₁₂ + ssig0 w₄ + ssig1 (w₁ + w₁₀ + ssig0 w₂ + ssig1 w₁₅)) := by
  simp only [xupd, alignRight_4, psrld_eq _ _ (by decide : (7 : BitVec 8).toNat < 32),
    psrld_eq _ _ (by decide : (3 : BitVec 8).toNat < 32), psrld_eq _ _ (by decide : (11 : BitVec 8).toNat < 32),
    psrld_eq _ _ (by decide : (10 : BitVec 8).toNat < 32),
    pslld_eq _ _ (by decide : (14 : BitVec 8).toNat < 32), pslld_eq _ _ (by decide : (11 : BitVec 8).toNat < 32),
    pxor_eq, xor_ofDwords, paddd_eq, shufDwords_fa, shufDwords_50, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3]
  simp only [psrlq_eq _ _ _ _ _ (by decide : (17 : BitVec 8).toNat < 32),
    psrlq_eq _ _ _ _ _ (by decide : (2 : BitVec 8).toNat < 32), pshufb_BA, pshufb_DC,
    dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]
  simp only [BitVec.reduceToNat, Nat.reduceSub, ssig0_shifts, ssig1_shifts,
    word_add_zero]

/-- `schedule` computes the next four words of a block's schedule. -/
theorem xupd_quad (M : Block) (i : Nat) :
    xupd (quad M i) (quad M (i + 1)) (quad M (i + 2)) (quad M (i + 3)) = quad M (i + 4) := by
  simp only [quad]
  rw [xupd_eq]
  have w0 : W M (4 * (i + 4)) = ssig1 (W M (4 * (i + 3) + 2)) + W M (4 * (i + 2) + 1) +
      ssig0 (W M (4 * i + 1)) + W M (4 * i) := W_ge' M (4 * i)
  have w1 : W M (4 * (i + 4) + 1) = ssig1 (W M (4 * (i + 3) + 3)) + W M (4 * (i + 2) + 2) +
      ssig0 (W M (4 * i + 2)) + W M (4 * i + 1) := W_ge' M (4 * i + 1)
  have w2 : W M (4 * (i + 4) + 2) = ssig1 (W M (4 * (i + 4))) + W M (4 * (i + 2) + 3) +
      ssig0 (W M (4 * i + 3)) + W M (4 * i + 2) := W_ge' M (4 * i + 2)
  have w3 : W M (4 * (i + 4) + 3) = ssig1 (W M (4 * (i + 4) + 1)) + W M (4 * (i + 3)) +
      ssig0 (W M (4 * (i + 1))) + W M (4 * i + 3) := W_ge' M (4 * i + 3)
  rw [w2, w3, w0, w1]
  ac_rfl

end VG.Proof.Sha256.X86_64.Avx2
