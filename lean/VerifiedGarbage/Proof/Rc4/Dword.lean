import VerifiedGarbage.Proof.Rc4.Memory

/-!
# RC4: scanning the table a doubleword at a time

Facts for implementations that visit the 256-byte table as 64 doublewords
at fixed addresses: the masks `sub` and `sbb` make, the bytes of a
doubleword, and a doubleword stored back XORed with a difference in one
byte. (`Qword.lean` has the same for quadwords.)
-/

namespace VG.Proof.Rc4
open VG

/-- `0 - CF`, as `sbb r, r` leaves it after a `sub`. -/
theorem borrow_mask32 (p : Bool) :
    (0#32 - (BitVec.ofBool p).setWidth 32) = if p then BitVec.allOnes 32 else 0#32 := by
  cases p <;> decide

theorem toNat_lt_four (x : BitVec 32) : x.toNat < 4 ↔ x >>> 2 = 0#32 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod]
  omega

/-- Byte `n` of the table is in doubleword `k` iff `n XOR 4k < 4`. -/
theorem row_hit32 (idx : Byte) {k : Nat} (hk : k < 64) :
    (idx.setWidth 32 ^^^ BitVec.ofNat 32 (4 * k)).toNat < 4 ↔ idx.toNat / 4 = k := by
  rw [toNat_lt_four, BitVec.ushiftRight_xor_distrib, BitVec.xor_eq_zero_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have := idx.isLt
  omega

/-- Byte `n` of the table is byte `j` of its doubleword iff `(n AND 3) XOR j < 1`. -/
theorem lane_hit32 (idx : Byte) {j : Nat} (hj : j < 4) :
    ((idx.setWidth 32 &&& BitVec.ofNat 32 3) ^^^ BitVec.ofNat 32 j).toNat < 1 ↔
      idx.toNat % 4 = j := by
  have h1 : ∀ x : BitVec 32, x.toNat < 1 ↔ x = 0#32 := by
    intro x
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
    omega
  rw [h1, BitVec.xor_eq_zero_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (3 % 2 ^ 32 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := idx.isLt
  omega

/-- The doubleword holding byte `n` of the table, and the byte's position in it. -/
theorem row_lane32 (p : Addr) (n : Nat) :
    p + BitVec.ofNat 64 (4 * (n / 4)) + BitVec.ofNat 64 (n % 4) = p + BitVec.ofNat 64 n := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod]

/-- Byte `L` of a little-endian doubleword, shifted down and masked. -/
theorem dword_byte (m : Mem) (a : Addr) {L : Nat} (hL : L < 4) :
    (m.readW a 32 >>> (8 * L)) &&& BitVec.ofNat 32 255 = (m (a + BitVec.ofNat 64 L)).setWidth 32 := by
  rw [← Mem.extractLsb'_read m a (n := 4) hL]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h255 : (BitVec.ofNat 32 255).getLsbD i = decide (i < 8) := by
    change Nat.testBit 255 i = decide (i < 8)
    exact Nat.testBit_two_pow_sub_one 8 i
  simp only [BitVec.getLsbD_and, h255, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', Mem.readW, Nat.reduceDiv]
  by_cases h : i < 8
  · simp [h, show 8 * L + i < 32 by omega, show i < 32 by omega]
  · simp [h]

/-- A doubleword shifted right by a byte more. -/
theorem shr_byte32 (x : BitVec 32) (j : Nat) : (x >>> (8 * j)) >>> 8 = x >>> (8 * (j + 1)) := by
  rw [← BitVec.shiftRight_add]
  rfl

/-- The bytes of a byte shifted left by whole bytes. -/
theorem shl_extract32 (c : Byte) {L e : Nat} (hL : L < 4) (he : e < 4) :
    ((c.setWidth 32) <<< (8 * L)).extractLsb' (8 * e) 8 = if e = L then c else 0#8 := by
  have hc : ∀ k, 8 ≤ k → c.getLsbD k = false := fun k hk => BitVec.getLsbD_of_ge c k hk
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and, show 8 * e + i < 32 by omega]
  by_cases h : e = L
  · subst h
    simp [show ¬ 8 * e + i < 8 * e by omega, show 8 * e + i - 8 * e = i by omega, hi,
      show i < 32 by omega]
  · by_cases hlt : e < L
    · simp [h, show 8 * e + i < 8 * L by omega]
    · simp [h, show ¬ 8 * e + i < 8 * L by omega, hc _ (show 8 ≤ 8 * e + i - 8 * L by omega)]

/-- Rotating right by 24 is a shift left by a byte, while the top byte is zero. -/
theorem rot_byte32 (c : Byte) {n : Nat} (hn : n < 3) :
    ((c.setWidth 32) <<< (8 * n)).rotateRight 24 = (c.setWidth 32) <<< (8 * (n + 1)) := by
  have hc : ∀ k, 8 ≤ k → c.getLsbD k = false := fun k hk => BitVec.getLsbD_of_ge c k hk
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    show 24 % 32 = 24 from rfl, show 32 - 24 = 8 from rfl, hi, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · simp [h8, show 24 + i < 32 by omega, show ¬ 24 + i < 8 * n by omega,
      show i < 8 * (n + 1) by omega, hc _ (show 8 ≤ 24 + i - 8 * n by omega)]
  · by_cases hlo : i - 8 < 8 * n
    · simp [h8, hlo, show i - 8 < 32 by omega, show i < 8 * (n + 1) by omega]
    · simp [h8, hlo, show i - 8 < 32 by omega, show ¬ i < 8 * (n + 1) by omega,
        show i - 8 - 8 * n = i - 8 * (n + 1) by omega]

/-- Storing back a doubleword XORed with `y` XORs each of its bytes with that of `y`. -/
theorem writeW_xor32 (m : Mem) (a : Addr) (y : BitVec 32) (x : Addr) :
    m.writeW a (m.readW a 32 ^^^ y) x =
      if (x - a).toNat < 4 then m x ^^^ y.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  change (if (x - a).toNat < 4 then ((m.readW a 32 ^^^ y).setWidth 32).extractLsb'
    (8 * (x - a).toNat) 8 else m x) = _
  by_cases h : (x - a).toNat < 4
  · rw [ite_eq_left h, ite_eq_left h, BitVec.setWidth_eq, BitVec.extractLsb'_xor]
    congr 1
    change ((m.read a 4).setWidth 32).extractLsb' (8 * (x - a).toNat) 8 = m x
    rw [BitVec.setWidth_eq, Mem.extractLsb'_read _ _ h, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_comm, BitVec.sub_add_cancel]
  · rw [ite_eq_right h, ite_eq_right h]

/-- Storing a doubleword back unchanged. -/
theorem writeW_readW32 (m : Mem) (a : Addr) : m.writeW a (m.readW a 32) = m := by
  funext x
  have h := writeW_xor32 m a 0#32 x
  rw [BitVec.xor_zero] at h
  rw [h]
  split
  · rw [show (0#32).extractLsb' (8 * (x - a).toNat) 8 = 0#8 by simp, BitVec.xor_zero]
  · rfl

/-- Storing back the doubleword that holds byte `n` of the table at `p`, XORed
with `c` shifted to the byte's position, XORs that byte with `c`. -/
theorem writeW_byte32 (m : Mem) (p : Addr) (n : Nat) (c : Byte) :
    m.writeW (p + BitVec.ofNat 64 (4 * (n / 4)))
      (m.readW (p + BitVec.ofNat 64 (4 * (n / 4))) 32 ^^^ (c.setWidth 32) <<< (8 * (n % 4))) =
    m.write (p + BitVec.ofNat 64 n) 1 (m (p + BitVec.ofNat 64 n) ^^^ c) := by
  funext x
  rw [writeW_xor32, write_byte]
  let q := p + BitVec.ofNat 64 (4 * (n / 4))
  have hq : p + BitVec.ofNat 64 n = q + BitVec.ofNat 64 (n % 4) := (row_lane32 p n).symm
  have hiff : ∀ e < 4, (x - q).toNat = e ↔ x = q + BitVec.ofNat 64 e := by
    intro e he
    constructor
    · intro h
      have h' : x - q = BitVec.ofNat 64 e := by
        apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [← h', BitVec.add_comm, BitVec.sub_add_cancel]
    · intro h; rw [h, Mem.sub_ofNat_toNat q (by omega)]
  change (if (x - q).toNat < 4 then m x ^^^ ((c.setWidth 32) <<< (8 * (n % 4))).extractLsb'
    (8 * (x - q).toNat) 8 else m x) = _
  rw [hq]
  by_cases hin : (x - q).toNat < 4
  · rw [ite_eq_left hin, shl_extract32 c (Nat.mod_lt _ (by decide)) hin]
    by_cases he : (x - q).toNat = n % 4
    · rw [ite_eq_left he, ite_eq_left ((hiff _ (Nat.mod_lt _ (by decide))).mp he)]
      rw [(hiff _ (Nat.mod_lt _ (by decide))).mp he]
    · rw [ite_eq_right he, BitVec.xor_zero, ite_eq_right]
      intro hx
      exact he ((hiff _ (Nat.mod_lt _ (by decide))).mpr hx)
  · rw [ite_eq_right hin, ite_eq_right]
    intro hx
    exact hin (by rw [hx, Mem.sub_ofNat_toNat q (by omega)]; exact Nat.mod_lt _ (by decide))

end VG.Proof.Rc4
