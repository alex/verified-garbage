import VerifiedGarbage.Proof.ChaCha20.Stream

/-!
# Streaming ChaCha20: words in memory, byte by byte

Untrusted: everything here is checked by Lean. Target-independent lemmas for
the 32-bit targets, which store the 64-bit number of bytes left as two
32-bit words and copy 16 bytes at a time: the bytes of a write and of a
read of any width, and a 64-bit word from its two halves.
-/

namespace VG.Proof.ChaCha20

open VG.Spec.ChaCha20 (leftAt)

/-- A byte of a little-endian write. -/
theorem byte_writeW_self (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) {i : Nat} (hi : i < w / 8)
    (hi' : i < 2 ^ 64) : (m.writeW a v) (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * i) 8 := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat a hi', hi, ite_true]
  ext k hk
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * i + k < 8 * (w / 8) := by omega
  simp [this]

/-- Byte `j` of a little-endian 128-bit word. -/
theorem readW128_byte (m : Mem) (a : Addr) {j : Nat} (hj : j < 16) :
    (m.readW a 128).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m a (n := 16) hj]
  simp only [Mem.readW]
  rfl

/-- Two 64-bit words with the same bytes are equal. -/
theorem word64_ext {x y : BitVec 64} (h : ∀ i < 8, x.extractLsb' (8 * i) 8 = y.extractLsb' (8 * i) 8) :
    x = y := by
  ext j hj
  have := congrArg (·.getLsbD (j % 8)) (h (j / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show j % 8 < 8 by omega, decide_true,
    Bool.true_and] at this
  rw [show 8 * (j / 8) + j % 8 = j by omega] at this
  simpa [BitVec.getLsbD_eq_getElem hj] using this

/-- The 64-bit number `v` from its two 32-bit halves, low first, written at
`p + e`. -/
theorem readW64_halves (m : Mem) (p : Addr) {e : Nat} (v : Nat) (he : e + 8 ≤ 2 ^ 32) :
    ((m.writeW (p + BitVec.ofNat 64 e) (BitVec.ofNat 32 v)).writeW (p + BitVec.ofNat 64 (e + 4))
      (BitVec.ofNat 32 (v / 2 ^ 32))).readW (p + BitVec.ofNat 64 e) 64 = BitVec.ofNat 64 v := by
  refine word64_ext fun j hj => ?_
  rw [readW64_byte _ _ hj, Offset.add_add]
  by_cases hlo : j < 4
  · rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), ← Offset.add_add p e j,
      byte_writeW_self _ _ _ (by omega) (by omega)]
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_ofNat]
    simp [show 8 * j + k < 32 by omega, show 8 * j + k < 64 by omega]
  · rw [show e + j = (e + 4) + (j - 4) by omega, ← Offset.add_add p (e + 4) (j - 4),
      byte_writeW_self _ _ _ (by omega) (by omega)]
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_ofNat, Nat.testBit_div_two_pow]
    simp [show 8 * (j - 4) + k < 32 by omega, show 8 * j + k < 64 by omega,
      show 8 * (j - 4) + k + 32 = 8 * j + k by omega]

/-- The number of bytes left, from its two halves. -/
theorem leftAt_halves (m : Mem) (p : Addr) {v : Nat} (hv : v < 2 ^ 64) :
    leftAt ((m.writeW (p + BitVec.ofNat 64 128) (BitVec.ofNat 32 v)).writeW (p + BitVec.ofNat 64 132)
      (BitVec.ofNat 32 (v / 2 ^ 32))) p = v := by
  simp only [leftAt]
  rw [show (p + 128 : Addr) = p + BitVec.ofNat 64 128 from rfl, readW64_halves m p (e := 128) v (by decide),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

/-- Byte `j` of two words, low first. -/
theorem append_byte (hi lo : BitVec 32) {j : Nat} (hj : j < 8) :
    (hi ++ lo).extractLsb' (8 * j) 8 = if j < 4 then lo.extractLsb' (8 * j) 8 else hi.extractLsb' (8 * (j - 4)) 8 := by
  by_cases h : j < 4
  · rw [ite_pos h]
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append, show 8 * j + k < 32 by omega, ite_true]
  · rw [ite_neg h]
    ext k hk
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append, show ¬ (8 * j + k < 32) by omega, ite_false]
    congr 1; omega

/-- A 64-bit word in memory is its two 32-bit halves, low first. -/
theorem readW64_split (m : Mem) (a : Addr) : m.readW a 64 = m.readW (a + BitVec.ofNat 64 4) 32 ++ m.readW a 32 := by
  refine word64_ext fun j hj => ?_
  rw [readW64_byte _ _ hj, append_byte _ _ hj]
  by_cases h : j < 4
  · rw [ite_pos h, ← Mem.readW_byte _ _ h]
  · rw [ite_neg h, ← Mem.readW_byte _ _ (by omega), Offset.add_add, show 4 + (j - 4) = j by omega]

theorem readW64_toNat (m : Mem) (a : Addr) :
    (m.readW a 64).toNat = (m.readW a 32).toNat + 2 ^ 32 * (m.readW (a + BitVec.ofNat 64 4) 32).toNat := by
  rw [readW64_split, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (m.readW a 32).isLt, Nat.shiftLeft_eq]
  omega

end VG.Proof.ChaCha20
