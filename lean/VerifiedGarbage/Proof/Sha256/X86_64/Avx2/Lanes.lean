import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Spec
import VerifiedGarbage.Impl.Sha256.X86_64.Avx2

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

/-- A quadword shift right, on doublewords: the high doubleword of each
quadword shifts into the low one. -/
theorem psrlq_eq (a c b d : BitVec 32) (n : BitVec 8) (h₀ : 0 < n.toNat) (h : n.toNat < 32) :
    XShiftOp.eval .psrlq (ofDwords a c b d) n =
      ofDwords (a >>> n.toNat ||| c <<< (32 - n.toNat)) (c >>> n.toNat)
        (b >>> n.toNat ||| d <<< (32 - n.toNat)) (d >>> n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, ofDwords, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or]
  generalize n.toNat = m at *
  obtain ⟨q, r, hq, hr, rfl⟩ : ∃ q r, q < 4 ∧ r < 32 ∧ i = 32 * q + r :=
    ⟨i / 32, i % 32, by omega, by omega, by omega⟩
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
  by_cases h4 : r < 32 - m <;>
  simp (disch := omega) only [h4, decide_true, decide_false, decide_eq_true,
    decide_eq_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.not_true,
    Bool.not_false, Bool.or_false, Bool.false_or, Nat.mul_zero, Nat.mul_one, Nat.zero_add,
    BitVec.getLsbD_of_ge, ite_eq_left, ite_eq_right] <;>
  first | exact congrArg _ (by omega)

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
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
    k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
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
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
    k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
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

/-- Split an equation of words into one per bit, at each of the 32 positions. -/
macro "bits32" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h))

/-- The bits of a word's shifts and rotations, at a known position. -/
macro "bits_simp" : tactic => `(tactic| (
  simp (disch := omega) only [ssig0, ssig1, BitVec.getLsbD_xor, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateRight, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMod, Nat.reduceLT, decide_true, decide_false, Bool.true_and,
    Bool.false_and, Bool.not_true, Bool.not_false, Bool.cond_false, BitVec.getLsbD_of_ge,
    Bool.xor_false, Bool.false_xor, Bool.or_false, Bool.false_or, ↓reduceIte] <;>
  simp only [Bool.xor_comm, Bool.xor_left_comm, Bool.xor_assoc]))

/-- `σ₀`, as `schedule` computes it: shifts by 3, 7, 14, 18 and 25. -/
theorem ssig0_shifts (x : Word) :
    (x >>> 3 ^^^ x >>> 7 ^^^ x <<< 14 ^^^ x >>> 7 >>> 11 ^^^ x <<< 14 <<< 11) = ssig0 x := by
  bits32 <;> bits_simp

/-- `σ₁`, as `schedule` computes it: shifts of the word doubled into a quadword. -/
theorem ssig1_shifts (x : Word) :
    (x >>> 10 ^^^ (x >>> 17 ||| x <<< 15) ^^^ ((x >>> 17 ||| x <<< 15) >>> 2 ||| x >>> 17 <<< 30)) =
      ssig1 x := by
  bits32 <;> bits_simp

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
  simp only [psrlq_eq _ _ _ _ _ (by decide : 0 < (17 : BitVec 8).toNat) (by decide),
    psrlq_eq _ _ _ _ _ (by decide : 0 < (2 : BitVec 8).toNat) (by decide), pshufb_BA, pshufb_DC,
    dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]
  simp only [BitVec.reduceToNat, Nat.reduceSub, ssig0_shifts, ssig1_shifts,
    word_add_zero]

/-- `schedule` computes the next four words of a block's schedule. -/
theorem xupd_quad (M : Block) (i : Nat) :
    xupd (quad M i) (quad M (i + 1)) (quad M (i + 2)) (quad M (i + 3)) = quad M (i + 4) := by
  simp only [quad]
  rw [xupd_eq]
  have w0 := W_ge' M (4 * i)
  have w1 := W_ge' M (4 * i + 1)
  have w2 := W_ge' M (4 * i + 2)
  have w3 := W_ge' M (4 * i + 3)
  simp only [show 4 * i + 16 = 4 * (i + 4) by omega, show 4 * i + 1 + 16 = 4 * (i + 4) + 1 by omega,
    show 4 * i + 2 + 16 = 4 * (i + 4) + 2 by omega, show 4 * i + 3 + 16 = 4 * (i + 4) + 3 by omega,
    show 4 * i + 14 = 4 * (i + 3) + 2 by omega, show 4 * i + 1 + 14 = 4 * (i + 3) + 3 by omega,
    show 4 * i + 9 = 4 * (i + 2) + 1 by omega, show 4 * i + 1 + 9 = 4 * (i + 2) + 2 by omega,
    show 4 * i + 2 + 9 = 4 * (i + 2) + 3 by omega, show 4 * i + 3 + 9 = 4 * (i + 3) by omega,
    show 4 * i + 1 + 1 = 4 * i + 2 by omega, show 4 * i + 2 + 1 = 4 * i + 3 by omega,
    show 4 * i + 3 + 1 = 4 * (i + 1) by omega] at w0 w1 w2 w3 ⊢
  rw [w2, w3, w0, w1]
  have e : ∀ a b c d : Word, a + b + c + d = d + b + c + a := by intro a b c d; ac_rfl
  simp only [e]

end VG.Proof.Sha256.X86_64.Avx2
