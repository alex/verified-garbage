import VerifiedGarbage.Proof.MlDsa.Sample.Word

/-!
# ML-DSA: the sign bits of `SampleInBall` in two 32-bit words

Untrusted: everything here is checked by Lean. An implementation with
32-bit words keeps the sign bits of `SampleInBall` not yet used, the first
8 bytes of the output as a little-endian integer `S` shifted right by the
number `t` of signs used, as two words: `S / 2^t` (modulo `2³²`) and
`S / 2^(t+32)`. They start as the two little-endian words of the bytes
(`readW_lo`, `readW_hi`); the next sign is the low bit of the first
(`signBit_eq`); and shifting the pair right by one bit is the first shifted
right by one plus the low bit of the second rotated to the top
(`signs_shift`).
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- A value less than `2ⁿ`, rotated right by `n`, is shifted left by `32 - n`. -/
theorem rotr_small32 (x : BitVec 32) {n : Nat} (h0 : 0 < n) (h : n < 32) (hx : x.toNat < 2 ^ n) :
    (x.rotateRight n).toNat = x.toNat * 2 ^ (32 - n) := by
  rw [BitVec.rotateRight_def, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  simp only [Nat.mod_eq_of_lt h]
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hx, Nat.zero_or, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have : x.toNat * 2 ^ (32 - n) < 2 ^ n * 2 ^ (32 - n) := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
  rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)] at this
  exact this

theorem and_one_toNat (x : BitVec 32) : (x &&& 1).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]

theorem leNat_lt : ∀ (v : List Byte), leNat v < 2 ^ (8 * v.length)
  | [] => by simp [leNat]
  | c :: v => by
    have ih := leNat_lt v
    have hc := c.isLt
    rw [leNat, List.length_cons, show 8 * (v.length + 1) = 8 * v.length + 8 by omega, Nat.pow_add]
    generalize 2 ^ (8 * v.length) = P at ih ⊢
    rw [show (2 : Nat) ^ 8 = 256 from rfl] at hc ⊢
    omega

/-- The high word shifted right by one bit. -/
theorem signs_shift_hi {S : Nat} (hS : S < 2 ^ 64) (t : Nat) :
    BitVec.ofNat 32 (S / 2 ^ (t + 32)) >>> 1 = BitVec.ofNat 32 (S / 2 ^ (t + 1 + 32)) := by
  have e : S / 2 ^ (t + 1 + 32) = S / 2 ^ (t + 32) / 2 := by
    rw [show t + 1 + 32 = t + 32 + 1 by omega, Nat.pow_succ, Nat.div_div_eq_div_mul]
  have hl : S / 2 ^ (t + 32) < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hS (Nat.pow_le_pow_right (by decide) (by omega))
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt (by omega)]

/-- The word at `a` whose bits `j < 32` are the bits `o + j` of `X`. -/
theorem readW_bits (m : Mem) (a : Addr) (X : List Byte) (o : Nat)
    (hb : ∀ b < 4, m (a + BitVec.ofNat 64 b) = X.getD (o / 8 + b) 0) (ho : o % 8 = 0) :
    m.readW a 32 = BitVec.ofNat 32 (leNat X / 2 ^ o) := by
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro j
  rw [BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 32
  · rw [← BitVec.getLsbD, readW32_getLsbD m a hj, hb (j / 8) (by omega), testBit_leNat,
      show (j + o) / 8 = o / 8 + j / 8 by omega, show (j + o) % 8 = j % 8 by omega]
    simp [hj]
  · simp only [hj, decide_false, Bool.false_and]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (m.readW a 32).isLt (Nat.pow_le_pow_right (by decide) (by omega)))

/-- The first word of the first 8 bytes of `X`. -/
theorem readW_lo (m : Mem) (a : Addr) (X : List Byte) (hb : ∀ b < 8, m (a + BitVec.ofNat 64 b) = X.getD b 0) :
    m.readW a 32 = BitVec.ofNat 32 (leNat (X.take 8) / 2 ^ 0) :=
  readW_bits m a (X.take 8) 0 (fun b h => by
    rw [Nat.zero_div, Nat.zero_add, hb b (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)])
    rfl

/-- The second word of the first 8 bytes of `X`. -/
theorem readW_hi (m : Mem) (a : Addr) (X : List Byte) (hb : ∀ b < 8, m (a + BitVec.ofNat 64 b) = X.getD b 0) :
    m.readW (a + 4) 32 = BitVec.ofNat 32 (leNat (X.take 8) / 2 ^ (0 + 32)) :=
  readW_bits m (a + 4) (X.take 8) 32 (fun b h => by
    rw [BitVec.add_assoc, show (4 : BitVec 64) + BitVec.ofNat 64 b = BitVec.ofNat 64 (4 + b) by
      rw [BitVec.ofNat_add]; rfl, hb (4 + b) (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega)]) rfl

/-- The next sign: the low bit of the first word. -/
theorem signBit_eq (S t : Nat) :
    (BitVec.ofNat 32 (S / 2 ^ t) &&& 1 == 0) = !(S.testBit t) := by
  have e : (BitVec.ofNat 32 (S / 2 ^ t) &&& 1).toNat = S / 2 ^ t % 2 := by
    rw [and_one_toNat, BitVec.toNat_ofNat]
    omega
  rw [testBit_eq]
  by_cases h : S / 2 ^ t % 2 = 1
  · simp only [h, decide_true, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    intro h'; rw [h'] at e; simp at e; omega
  · simp only [h, decide_false, Bool.not_false, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq (by rw [e]; simp; omega)

/-- The pair of words shifted right by one bit. -/
theorem signs_shift (S t : Nat) :
    BitVec.ofNat 32 (S / 2 ^ t) >>> 1 + (BitVec.ofNat 32 (S / 2 ^ (t + 32)) &&& 1).rotateRight 1 =
      BitVec.ofNat 32 (S / 2 ^ (t + 1)) := by
  have e1 : S / 2 ^ (t + 1) = S / 2 ^ t / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  have e2 : S / 2 ^ (t + 32) = S / 2 ^ (t + 1) / 2 ^ 31 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  generalize S / 2 ^ t = A at e1
  rw [e2, e1]
  generalize hB : A / 2 = B
  have hm : (BitVec.ofNat 32 (B / 2 ^ 31) &&& 1).toNat = B / 2 ^ 31 % 2 := by
    rw [and_one_toNat, BitVec.toNat_ofNat]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    rotr_small32 _ (by decide) (by decide) (by rw [hm]; omega), hm, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

end VG.Proof.MlDsa.Sample
