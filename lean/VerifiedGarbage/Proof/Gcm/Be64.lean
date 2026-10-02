import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Gcm.Bits

/-!
# GCM: the lengths block from byte-reversed words

Untrusted: everything here is checked by Lean. A 64-bit word stored
little-endian after a byte reversal (`byteRev64`) is the big-endian
`[x]₆₄` of its value (`le8_byteRev64`), which is `be64` modulo 2⁶⁴
(`be64_mod`).
-/

namespace VG.Proof.Gcm

open VG VG.Spec.Gcm

theorem be64_mod (x : Nat) : be64 (x % 2 ^ 64) = be64 x := by
  simp only [be64]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have h : 2 ^ 64 = 256 ^ (7 - i) * 256 ^ (i + 1) := by
    rw [← Nat.pow_add, show 7 - i + (i + 1) = 8 by omega]
  rw [h, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (show 2 ^ 8 ∣ 256 ^ (i + 1) from
    ⟨256 ^ i, by rw [Nat.pow_succ, Nat.mul_comm]⟩)]

theorem byte_extract (w : BitVec 64) (i : Nat) :
    w.extractLsb' (8 * i) 8 = BitVec.ofNat 8 (w.toNat / 256 ^ i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem byteRev64_extract (w : BitVec 64) {i : Nat} (hi : i < 8) :
    (byteRev64 w).extractLsb' (8 * i) 8 = w.extractLsb' (8 * (7 - i)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and]
  rw [getLsbD_byteRev64 _ _ (by omega)]
  congr 1; omega

/-- A byte-reversed word, as its 8 little-endian bytes: `[x]₆₄`. -/
theorem le8_byteRev64 (w : BitVec 64) : Cmac.le8 (byteRev64 w) = be64 w.toNat := by
  simp only [Cmac.le8, be64]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [byteRev64_extract w hi, byte_extract w]

end VG.Proof.Gcm
