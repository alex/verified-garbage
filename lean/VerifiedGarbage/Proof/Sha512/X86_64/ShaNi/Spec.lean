import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Schedule
import VerifiedGarbage.TCB.X86_64.Avx

/-!
# SHA-512 with the SHA512 extension: the values in the AVX registers

Untrusted: everything here is checked by Lean. How the working variables and
the message schedule are laid out in the 128-bit lanes of the AVX registers,
and that `vsha512rnds2` and `vsha512msg1`/`vsha512msg2` compute rounds and
schedule words of `Spec/Sha512.lean`.
-/

namespace VG.Proof.Sha512.X86_64.ShaNi

open VG VG.X86_64
open VG.Spec.Sha512 (HashValue Word Block K W ch maj bsig0 bsig1 ssig0 ssig1)
open VG.Proof.Sha512.X86_64.Avx2 (pair qword_append_0 qword_append_1 paddq_eq alignRight_8 W_ge')

/-! ## Quadwords of 128- and 256-bit values -/

theorem app4 (a b c d : Word) : a ++ b ++ c ++ d = (a ++ b) ++ (c ++ d) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append]
  split_ifs <;> first | omega | exact congrArg _ (by omega)

theorem lo64 (a b : Word) : (a ++ b).extractLsb' 0 64 = b := BitVec.extractLsb'_append_eq_right
theorem hi64 (a b : Word) : (a ++ b).extractLsb' 64 64 = a := BitVec.extractLsb'_append_eq_left
theorem lo128 (a b : BitVec 128) : (a ++ b).extractLsb' 0 128 = b := BitVec.extractLsb'_append_eq_right
theorem hi128 (a b : BitVec 128) : (a ++ b).extractLsb' 128 128 = a := BitVec.extractLsb'_append_eq_left

theorem lo4 (a b c d : Word) : (a ++ b ++ c ++ d : BitVec 256).extractLsb' 0 128 = c ++ d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and]
  split_ifs <;> first | omega | exact congrArg _ (by omega)

theorem hi4 (a b c d : Word) : (a ++ b ++ c ++ d : BitVec 256).extractLsb' 128 128 = a ++ b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and]
  split_ifs <;> first | omega | exact congrArg _ (by omega)

/-- A 256-bit value is its upper lane followed by its lower one. -/
theorem split256 (x : BitVec 256) : x.extractLsb' 128 128 ++ x.extractLsb' 0 128 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  by_cases h : i < 128
  · simp only [h, ite_true, decide_true, Bool.true_and, Nat.zero_add]
  · simp only [h, ite_false, decide_eq_true (show i - 128 < 128 by omega), Bool.true_and]
    exact congrArg _ (by omega)

theorem qword256_0 (a b c d : Word) : qword256 ((a ++ b) ++ (c ++ d)) 0 = d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword256, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi,
    Bool.true_and]
  split_ifs <;> first | omega | exact congrArg _ (by omega)

theorem qword256_1 (a b c d : Word) : qword256 ((a ++ b) ++ (c ++ d)) 1 = c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword256, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi,
    Bool.true_and]
  split_ifs <;> first | omega | exact congrArg _ (by omega)

theorem qword256_2 (a b c d : Word) : qword256 ((a ++ b) ++ (c ++ d)) 2 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword256, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi,
    Bool.true_and]
  split_ifs <;> first | omega | exact congrArg _ (by omega)

theorem qword256_3 (a b c d : Word) : qword256 ((a ++ b) ++ (c ++ d)) 3 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword256, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi,
    Bool.true_and]
  split_ifs <;> first | omega | exact congrArg _ (by omega)

/-! ## The working variables -/

/-- Lane 0 of the working variables `A, B, E, F` as `vsha512rnds2` takes and
returns them: `E, F` (`F` in bits 63:0). -/
def abef0 (v : HashValue) : BitVec 128 := v[4] ++ v[5]

/-- Lane 1 of `A, B, E, F`: `A, B` (`A` in bits 127:64, bits 255:192 of the register). -/
def abef1 (v : HashValue) : BitVec 128 := v[0] ++ v[1]

/-- Lane 0 of `C, D, G, H`: `G, H`. -/
def cdgh0 (v : HashValue) : BitVec 128 := v[6] ++ v[7]

/-- Lane 1 of `C, D, G, H`: `C, D`. -/
def cdgh1 (v : HashValue) : BitVec 128 := v[2] ++ v[3]

/-- After two rounds, `C, D, G, H` are the old `A, B, E, F`. -/
theorem cdgh0_two (v : HashValue) (k0 w0 k1 w1 : Word) :
    cdgh0 (roundKW (roundKW v k0 w0) k1 w1) = abef0 v := rfl

theorem cdgh1_two (v : HashValue) (k0 w0 k1 w1 : Word) :
    cdgh1 (roundKW (roundKW v k0 w0) k1 w1) = abef1 v := rfl

theorem ch_eq : sha512Ch = ch := by
  funext x y z; simp only [sha512Ch, ch, BitVec.and_comm z]

/-- `vsha512rnds2` does two rounds, given `Wₜ + Kₜ` for them in the low quadwords of `x`. -/
theorem rnds2_eq (v : HashValue) (x : BitVec 128) {k0 w0 k1 w1 : Word}
    (h0 : x.extractLsb' 0 64 = k0 + w0) (h1 : x.extractLsb' 64 64 = k1 + w1) :
    sha512Rnds2 (cdgh1 v ++ cdgh0 v) (abef1 v ++ abef0 v) x =
      abef1 (roundKW (roundKW v k0 w0) k1 w1) ++ abef0 (roundKW (roundKW v k0 w0) k1 w1) := by
  have emaj : sha512Maj = maj := rfl
  have es0 : sha512BigSigma0 = bsig0 := rfl
  have es1 : sha512BigSigma1 = bsig1 := rfl
  simp only [sha512Rnds2, abef0, abef1, cdgh0, cdgh1, qword256_0, qword256_1, qword256_2,
    qword256_3, h0, h1, ch_eq, emaj, es0, es1, roundKW_0, roundKW_1, roundKW_2, roundKW_3, roundKW_4, roundKW_5, roundKW_6, roundKW_7]
  rw [app4]
  generalize v[0]'(by decide) = a
  generalize v[1]'(by decide) = b
  generalize v[2]'(by decide) = c
  generalize v[3]'(by decide) = d
  generalize v[4]'(by decide) = e
  generalize v[5]'(by decide) = f
  generalize v[6]'(by decide) = g
  generalize v[7]'(by decide) = h
  have e1 : ch e f g + bsig1 e + (k0 + w0) + h + d = d + (h + bsig1 e + ch e f g + k0 + w0) := by ac_rfl
  have a1 : ch e f g + bsig1 e + (k0 + w0) + h + maj a b c + bsig0 a =
      h + bsig1 e + ch e f g + k0 + w0 + (bsig0 a + maj a b c) := by ac_rfl
  rw [e1, a1]
  generalize d + (h + bsig1 e + ch e f g + k0 + w0) = e₁
  generalize h + bsig1 e + ch e f g + k0 + w0 + (bsig0 a + maj a b c) = a₁
  have e2 : ch e₁ e f + bsig1 e₁ + (k1 + w1) + g + c = c + (g + bsig1 e₁ + ch e₁ e f + k1 + w1) := by ac_rfl
  have a2 : ch e₁ e f + bsig1 e₁ + (k1 + w1) + g + maj a₁ a b + bsig0 a₁ =
      g + bsig1 e₁ + ch e₁ e f + k1 + w1 + (bsig0 a₁ + maj a₁ a b) := by ac_rfl
  rw [e2, a2]

/-! ## The message schedule -/

/-- Lane 0 of the message schedule words `W₄ᵢ … W₄ᵢ₊₃`: `W₄ᵢ₊₁, W₄ᵢ` (`W₄ᵢ` in bits 63:0). -/
abbrev quad0 (M : Block) (i : Nat) : BitVec 128 := pair M (2 * i)

/-- Lane 1: `W₄ᵢ₊₃, W₄ᵢ₊₂`. -/
abbrev quad1 (M : Block) (i : Nat) : BitVec 128 := pair M (2 * i + 1)

theorem W_ge_rev (M : Block) (t : Nat) :
    W M (t + 16) = W M t + ssig0 (W M (t + 1)) + W M (t + 9) + ssig1 (W M (t + 14)) := by
  rw [W_ge' M t]; ac_rfl

/-- `vsha512msg1`, `vperm2i128` and `vpalignr` (for `Wₜ₋₇`), `vpaddq` and
`vsha512msg2` compute the next four schedule words from the previous sixteen. -/
theorem schedule_eq (M : Block) (i : Nat) :
    let m := sha512Msg1 (quad1 M i ++ quad0 M i) (quad0 M (i + 1))
    sha512Msg2 (XBinOp.eval .paddq (m.extractLsb' 128 128) (alignRight (quad0 M (i + 3)) (quad1 M (i + 2)) 8) ++
        XBinOp.eval .paddq (m.extractLsb' 0 128) (alignRight (quad1 M (i + 2)) (quad0 M (i + 2)) 8))
      (quad1 M (i + 3) ++ quad0 M (i + 3)) = quad1 M (i + 4) ++ quad0 M (i + 4) := by
  have ess0 : sha512Sigma0 = ssig0 := rfl
  have ess1 : sha512Sigma1 = ssig1 := rfl
  simp only [quad0, quad1, pair, sha512Msg1, sha512Msg2, qword256_0, qword256_1, qword256_2,
    qword256_3, lo64, lo4, hi4, alignRight_8, paddq_eq, ess0, ess1]
  have w0 := W_ge_rev M (4 * i)
  have w1 := W_ge_rev M (4 * i + 1)
  have w2 := W_ge_rev M (4 * i + 2)
  have w3 := W_ge_rev M (4 * i + 3)
  simp only [Nat.mul_add, ← Nat.mul_assoc, Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at w0 w1 w2 w3 ⊢
  rw [w2, w3, w0, w1, app4]

/-! ## Adding the working variables into the hash value, a lane at a time -/

theorem paddq_abef0 (v H : HashValue) :
    XBinOp.eval .paddq (abef0 v) (abef0 H) = abef0 (Vector.zipWith (· + ·) v H) := by
  simp only [abef0, paddq_eq, Vector.getElem_zipWith]

theorem paddq_abef1 (v H : HashValue) :
    XBinOp.eval .paddq (abef1 v) (abef1 H) = abef1 (Vector.zipWith (· + ·) v H) := by
  simp only [abef1, paddq_eq, Vector.getElem_zipWith]

theorem paddq_cdgh0 (v H : HashValue) :
    XBinOp.eval .paddq (cdgh0 v) (cdgh0 H) = cdgh0 (Vector.zipWith (· + ·) v H) := by
  simp only [cdgh0, paddq_eq, Vector.getElem_zipWith]

theorem paddq_cdgh1 (v H : HashValue) :
    XBinOp.eval .paddq (cdgh1 v) (cdgh1 H) = cdgh1 (Vector.zipWith (· + ·) v H) := by
  simp only [cdgh1, paddq_eq, Vector.getElem_zipWith]

end VG.Proof.Sha512.X86_64.ShaNi
