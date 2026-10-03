import VerifiedGarbage.Proof.Rc4.Memory

/-!
# RC4: scanning the table a quadword at a time

Facts for implementations that visit the 256-byte table as 32 quadwords at
fixed addresses: the masks `sub` and `sbb` make, the bytes of a quadword,
and a quadword stored back XORed with a difference in one byte.
-/

namespace VG.Proof.Rc4
open VG

/-- `0 - CF`, as `sbb r, r` leaves it after a `sub`. -/
theorem borrow_mask (p : Bool) :
    (0#64 - (BitVec.ofBool p).setWidth 64) = if p then BitVec.allOnes 64 else 0#64 := by
  cases p <;> decide

theorem toNat_lt_eight (x : BitVec 64) : x.toNat < 8 ↔ x >>> 3 = 0#64 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod]
  omega

/-- Byte `n` of the table is in quadword `k` iff `n XOR 8k < 8`. -/
theorem row_hit (idx : Byte) {k : Nat} (hk : k < 32) :
    (idx.setWidth 64 ^^^ BitVec.ofNat 64 (8 * k)).toNat < 8 ↔ idx.toNat / 8 = k := by
  rw [toNat_lt_eight, BitVec.ushiftRight_xor_distrib, BitVec.xor_eq_zero_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have := idx.isLt
  omega

/-- Byte `n` of the table is byte `j` of its quadword iff `(n AND 7) XOR j < 1`. -/
theorem lane_hit (idx : Byte) {j : Nat} (hj : j < 8) :
    ((idx.setWidth 64 &&& BitVec.ofNat 64 7) ^^^ BitVec.ofNat 64 j).toNat < 1 ↔
      idx.toNat % 8 = j := by
  have h1 : ∀ x : BitVec 64, x.toNat < 1 ↔ x = 0#64 := by
    intro x
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]
    omega
  rw [h1, BitVec.xor_eq_zero_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (7 % 2 ^ 64 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := idx.isLt
  omega

/-- The quadword holding byte `n` of the table, and the byte's position in it. -/
theorem row_lane (p : Addr) (n : Nat) :
    p + BitVec.ofNat 64 (8 * (n / 8)) + BitVec.ofNat 64 (n % 8) = p + BitVec.ofNat 64 n := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod]

/-- Byte `L` of a little-endian quadword, shifted down and masked. -/
theorem qword_byte (m : Mem) (a : Addr) {L : Nat} (hL : L < 8) :
    (m.readW a 64 >>> (8 * L)) &&& BitVec.ofNat 64 255 = (m (a + BitVec.ofNat 64 L)).setWidth 64 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hL]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h255 : (BitVec.ofNat 64 255).getLsbD i = decide (i < 8) := by
    change Nat.testBit 255 i = decide (i < 8)
    exact Nat.testBit_two_pow_sub_one 8 i
  simp only [BitVec.getLsbD_and, h255, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', Mem.readW, Nat.reduceDiv]
  by_cases h : i < 8
  · simp [h, show 8 * L + i < 64 by omega, show i < 64 by omega]
  · simp [h]

/-- A quadword shifted right by a byte more. -/
theorem shr_byte (x : BitVec 64) (j : Nat) : (x >>> (8 * j)) >>> 8 = x >>> (8 * (j + 1)) := by
  rw [← BitVec.shiftRight_add]
  rfl

/-- The bytes of a byte shifted left by whole bytes. -/
theorem shl_extract (c : Byte) {L e : Nat} (hL : L < 8) (he : e < 8) :
    ((c.setWidth 64) <<< (8 * L)).extractLsb' (8 * e) 8 = if e = L then c else 0#8 := by
  have hc : ∀ k, 8 ≤ k → c.getLsbD k = false := fun k hk => BitVec.getLsbD_of_ge c k hk
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and, show 8 * e + i < 64 by omega]
  by_cases h : e = L
  · subst h
    simp [show ¬ 8 * e + i < 8 * e by omega, show 8 * e + i - 8 * e = i by omega, hi,
      show i < 64 by omega]
  · by_cases hlt : e < L
    · simp [h, show 8 * e + i < 8 * L by omega]
    · simp [h, show ¬ 8 * e + i < 8 * L by omega, hc _ (show 8 ≤ 8 * e + i - 8 * L by omega)]

/-- Rotating right by 56 is a shift left by a byte, while the top byte is zero. -/
theorem rot_byte (c : Byte) {n : Nat} (hn : n < 7) :
    ((c.setWidth 64) <<< (8 * n)).rotateRight 56 = (c.setWidth 64) <<< (8 * (n + 1)) := by
  have hc : ∀ k, 8 ≤ k → c.getLsbD k = false := fun k hk => BitVec.getLsbD_of_ge c k hk
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    show 56 % 64 = 56 from rfl, show 64 - 56 = 8 from rfl, hi, decide_true, Bool.true_and]
  by_cases h8 : i < 8
  · simp [h8, show 56 + i < 64 by omega, show ¬ 56 + i < 8 * n by omega,
      show i < 8 * (n + 1) by omega, hc _ (show 8 ≤ 56 + i - 8 * n by omega)]
  · by_cases hlo : i - 8 < 8 * n
    · simp [h8, hlo, show i - 8 < 64 by omega, show i < 8 * (n + 1) by omega]
    · simp [h8, hlo, show i - 8 < 64 by omega, show ¬ i < 8 * (n + 1) by omega,
        show i - 8 - 8 * n = i - 8 * (n + 1) by omega]

/-- Storing back a quadword XORed with `y` XORs each of its bytes with that of `y`. -/
theorem writeW_xor (m : Mem) (a : Addr) (y : BitVec 64) (x : Addr) :
    m.writeW a (m.readW a 64 ^^^ y) x =
      if (x - a).toNat < 8 then m x ^^^ y.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  change (if (x - a).toNat < 8 then ((m.readW a 64 ^^^ y).setWidth 64).extractLsb'
    (8 * (x - a).toNat) 8 else m x) = _
  by_cases h : (x - a).toNat < 8
  · rw [ite_eq_left h, ite_eq_left h, BitVec.setWidth_eq, BitVec.extractLsb'_xor]
    congr 1
    change ((m.read a 8).setWidth 64).extractLsb' (8 * (x - a).toNat) 8 = m x
    rw [BitVec.setWidth_eq, Mem.extractLsb'_read _ _ h, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_comm, BitVec.sub_add_cancel]
  · rw [ite_eq_right h, ite_eq_right h]

/-- Storing a quadword back unchanged. -/
theorem writeW_readW (m : Mem) (a : Addr) : m.writeW a (m.readW a 64) = m := by
  funext x
  have h := writeW_xor m a 0#64 x
  rw [BitVec.xor_zero] at h
  rw [h]
  split
  · rw [show (0#64).extractLsb' (8 * (x - a).toNat) 8 = 0#8 by simp, BitVec.xor_zero]
  · rfl

/-- Storing back the quadword at `q` that holds byte `n` of the table at `p`,
XORed with `c` shifted to the byte's position, XORs that byte with `c`. -/
theorem writeW_byte (m : Mem) (p : Addr) (n : Nat) (c : Byte) :
    m.writeW (p + BitVec.ofNat 64 (8 * (n / 8)))
      (m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 64 ^^^ (c.setWidth 64) <<< (8 * (n % 8))) =
    m.write (p + BitVec.ofNat 64 n) 1 (m (p + BitVec.ofNat 64 n) ^^^ c) := by
  funext x
  rw [writeW_xor, write_byte]
  let q := p + BitVec.ofNat 64 (8 * (n / 8))
  have hq : p + BitVec.ofNat 64 n = q + BitVec.ofNat 64 (n % 8) := (row_lane p n).symm
  have hiff : ∀ e < 8, (x - q).toNat = e ↔ x = q + BitVec.ofNat 64 e := by
    intro e he
    constructor
    · intro h
      have h' : x - q = BitVec.ofNat 64 e := by
        apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [← h', BitVec.add_comm, BitVec.sub_add_cancel]
    · intro h; rw [h, Mem.sub_ofNat_toNat q (by omega)]
  change (if (x - q).toNat < 8 then m x ^^^ ((c.setWidth 64) <<< (8 * (n % 8))).extractLsb'
    (8 * (x - q).toNat) 8 else m x) = _
  rw [hq]
  by_cases hin : (x - q).toNat < 8
  · rw [ite_eq_left hin, shl_extract c (Nat.mod_lt _ (by decide)) hin]
    by_cases he : (x - q).toNat = n % 8
    · rw [ite_eq_left he, ite_eq_left ((hiff _ (Nat.mod_lt _ (by decide))).mp he)]
      rw [(hiff _ (Nat.mod_lt _ (by decide))).mp he]
    · rw [ite_eq_right he, BitVec.xor_zero, ite_eq_right]
      intro hx
      exact he ((hiff _ (Nat.mod_lt _ (by decide))).mpr hx)
  · rw [ite_eq_right hin, ite_eq_right]
    intro hx
    exact hin (by rw [hx, Mem.sub_ofNat_toNat q (by omega)]; exact Nat.mod_lt _ (by decide))

end VG.Proof.Rc4
