import VerifiedGarbage.Proof.CmacTripleDes.Bytes
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Block

/-!
# TDEA-CMAC: the specification with 8-byte blocks

`Proof/Cmac/Spec.lean` and `Proof/Cmac/Block.lean` for 8-byte blocks: the
MAC of whole blocks and the last bytes (`macFull_split8`), the padded last
block in memory (`padded_bytes8`), and TDEA's subkeys as 64-bit integers
(`subkeys_tdes`).
-/

namespace VG.Proof.CmacTripleDes

open VG Spec.Cmac Proof.Cmac

theorem blocks_eq8 {msg : List Byte} (last : List Byte) (q : Nat) (hq : msg.length = 8 * q) :
    (List.range q).map (fun i => ((msg ++ last).drop (8 * i)).take 8) = blocks 8 msg := by
  simp only [blocks, hq, Nat.mul_div_cancel_left _ (by decide : 0 < 8)]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

/-- §6.2 steps 3–6, for a message of whole blocks `msg` followed by `last`. -/
theorem macFull_split8 (ciph : Cipher) {msg last : List Byte} (hm : msg.length % 8 = 0)
    (hl : last.length ≤ 8) (hne : msg = [] ∨ 0 < last.length) :
    macFull ciph 8 (msg ++ last) =
      ciph (xor (chain ciph (zeros 8) (blocks 8 msg))
        (lastBlock 8 (subkeys ciph 8).1 (subkeys ciph 8).2 last)) := by
  obtain ⟨q, hq⟩ : ∃ q, msg.length = 8 * q := ⟨msg.length / 8, by omega⟩
  have hn : (if (msg ++ last).length = 0 then 1 else ((msg ++ last).length + 8 - 1) / 8) = q + 1 := by
    rw [List.length_append]
    split
    · omega
    · have hl0 : 0 < last.length := by
        rcases hne with h | h
        · subst h; simp only [List.length_nil] at *; omega
        · exact h
      omega
  simp only [macFull, hn, Nat.add_sub_cancel]
  rw [blocks_eq8 last q hq, chain_append, chain_single,
    List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append]

open VG.WriteBytes in
/-- The padded last block `Mₙ* ‖ 10ʲ`, from the bytes copied onto zeros. -/
theorem padded_bytes8 (m : Mem) (C : Addr) (xs : List Byte) (hL : xs.length < 8)
    (hz : Spec.Aes.bytesAt m C 8 = zeros 8) :
    Spec.Aes.bytesAt ((writeBytes m C xs).writeW (C + BitVec.ofNat 64 xs.length) (0x80 : Byte)) C 8 =
      xs ++ [0x80] ++ zeros (8 - xs.length - 1) := by
  refine ext8 (by simp [Spec.Aes.bytesAt]) (by simp [zeros]; omega) fun k hk => ?_
  rw [getD_bytesAt _ _ hk, writeW8_apply]
  have hz' : m (C + BitVec.ofNat 64 k) = 0 := by
    have := congrArg (fun l => l.getD k 0) hz
    rw [getD_bytesAt _ _ hk] at this
    rw [this]; simp only [zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate, hk,
      ite_true, Option.getD_some]
  have hsub : (C + BitVec.ofNat 64 k - C).toNat = k := Mem.sub_ofNat_toNat C (by omega)
  have heq : (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) ↔ k = xs.length := by
    constructor
    · intro h
      have := congrArg (fun a => (a - C).toNat) h
      simp only [Mem.sub_ofNat_toNat C (show k < 2 ^ 64 by omega),
        Mem.sub_ofNat_toNat C (show xs.length < 2 ^ 64 by omega)] at this
      exact this
    · intro h; rw [h]
  rcases Nat.lt_trichotomy k xs.length with h | h | h
  · have hne : ¬ (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) := by rw [heq]; omega
    simp only [hne, ite_false, writeBytes, hsub, h, ite_true]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · have hne : ¬ (C + BitVec.ofNat 64 k = C + BitVec.ofNat 64 xs.length) := by rw [heq]; omega
    simp only [hne, ite_false, writeBytes, hsub, show ¬ k < xs.length by omega, hz']
    obtain ⟨j, hj⟩ : ∃ j, k - xs.length = j + 1 := ⟨k - xs.length - 1, by omega⟩
    rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (show xs.length ≤ k by omega),
      hj, List.singleton_append, List.getElem?_cons_succ, zeros, List.getElem?_replicate]
    simp only [show j < 8 - xs.length - 1 by omega, ite_true, Option.getD_some]

/-- TDEA's subkeys: `L = CIPH_K(0⁶⁴)` doubled once and twice, as 64-bit integers. -/
theorem subkeys_tdes (S : Spec.TripleDes.Schedule) :
    subkeys (tdesWith S) 8 =
      (le8 (byteRev64 (dbl64 (tdes S 0))), le8 (byteRev64 (dbl64 (dbl64 (tdes S 0))))) := by
  have hz : zeros 8 = le8 0 := le8_zero.symm
  have hr : byteRev64 0 = 0 := by decide
  simp only [subkeys, hz, tdesWith_le8, hr, dbl_le8]

/-! ## The key schedule from the key's bytes -/

/-- The offset of DES key `i` in a TDEA key of `n` bytes. -/
def keyOff (n i : Nat) : Nat := if i = 2 ∧ n = 16 then 0 else 8 * i

/-- Slot `16 i + j` of the key schedule: round key `j` of DES key `i`. -/
theorem expandKey_getD (key : List Byte) {i j : Nat} (hi : i < 3) (hj : j < 16) :
    (Spec.TripleDes.expandKey key).getD (16 * i + j) 0 =
      ((Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Vector.ofFn fun t => key.getD (keyOff key.length i + t.val) 0))).getD j 0).zeroExtend 64 := by
  rw [vgetD _ (by omega), Spec.TripleDes.expandKey, Vector.getElem_ofFn]
  simp only [show (16 * i + j) % 16 = j by omega, keyOff]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · simp [show j < 16 from hj]
  · simp [show ¬ 16 + j < 16 by omega, show 16 + j < 32 by omega]
  · simp [show ¬ 32 + j < 16 by omega, show ¬ 32 + j < 32 by omega]

/-- A DES key in memory, as a big-endian integer. -/
theorem decode_bytesAt (m : Mem) (p : Addr) {n off : Nat} (h : off + 8 ≤ n) :
    Spec.TripleDes.decodeBlock (Vector.ofFn fun t => (Spec.Aes.bytesAt m p n).getD (off + t.val) 0) =
      byteRev64 (m.readW (p + BitVec.ofNat 64 off) 64) := by
  rw [← decode_le8, le8_readW]
  congr 1
  apply Vector.ext
  intro t ht
  simp only [Vector.getElem_ofFn]
  rw [getD_bytesAt _ _ (by omega), getD_bytesAt _ _ ht, Offset.add_add]

theorem msb_shift (y : BitVec 64) : y >>> 63 = if y.msb then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  have := y.isLt
  by_cases hm : 2 ^ (64 - 1) ≤ y.toNat
  · rw [decide_eq_true hm]; simp; omega
  · rw [decide_eq_false hm]; simp; omega

/-- The doubling as `init` computes it. -/
theorem dbl64_eq (y : BitVec 64) :
    (y + y) ^^^ (((0 : BitVec 64) - (y >>> 63)) &&& BitVec.signExtend 64 (0x1b : BitVec 32)) = dbl64 y := by
  have h : y + y = y <<< 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  rw [h, msb_shift, dbl64]
  congr 1
  split <;> decide

end VG.Proof.CmacTripleDes
