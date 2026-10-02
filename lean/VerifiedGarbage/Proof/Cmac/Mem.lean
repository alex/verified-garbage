import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CMAC: blocks in memory as 64-bit words

A 16-byte block is loaded and stored as two little-endian 64-bit words:
`le8 w` is the bytes of the word `w`, so the bytes at `p` are
`le8 (readW p) ++ le8 (readW (p + BitVec.ofNat 64 8))`, and storing `w₀` at `p` and `w₁` at
`p + 8` leaves `le8 w₀ ++ le8 w₁` there.
-/

namespace VG.Proof.Cmac

open VG Spec.Cmac

/-- The bytes of a 64-bit word, least significant first. -/
def le8 (w : BitVec 64) : List Byte := (List.range 8).map fun i => w.extractLsb' (8 * i) 8

theorem length_le8 (w : BitVec 64) : (le8 w).length = 8 := by simp [le8]

theorem getD_le8 (w : BitVec 64) {k : Nat} (hk : k < 8) : (le8 w).getD k 0 = w.extractLsb' (8 * k) 8 := by
  simp [le8, List.getD_eq_getElem?_getD, hk]

theorem getD_bytesAt (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) :
    (Spec.Aes.bytesAt m p n).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  simp [Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, hk]

theorem le8_readW (m : Mem) (a : Addr) : le8 (m.readW a 64) = Spec.Aes.bytesAt m a 8 := by
  apply List.ext_getElem (by simp [le8, Spec.Aes.bytesAt])
  intro k h₁ h₂
  have hk : k < 8 := by simpa [le8] using h₁
  simp only [le8, Spec.Aes.bytesAt, List.getElem_map, List.getElem_range]
  rw [← Mem.extractLsb'_read m a (n := 8) hk]
  simp only [Mem.readW]
  rfl

theorem le8_xor (a b : BitVec 64) : le8 (a ^^^ b) = Spec.Cmac.xor (le8 a) (le8 b) := by
  apply List.ext_getElem (by simp [le8, Spec.Cmac.xor])
  intro k h₁ h₂
  have hk : k < 8 := by simpa [le8] using h₁
  simp only [le8, Spec.Cmac.xor, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  ext j hj
  simp

theorem le8_zero : le8 0 = zeros 8 := by decide

theorem bytesAt_split (m : Mem) (p : Addr) :
    Spec.Aes.bytesAt m p 16 = Spec.Aes.bytesAt m p 8 ++ Spec.Aes.bytesAt m (p + BitVec.ofNat 64 8) 8 := by
  simp only [Spec.Aes.bytesAt]
  rw [show (16 : Nat) = 8 + 8 from rfl, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

/-- The bytes of a block after storing its two words. -/
theorem bytesAt_store2 (m : Mem) (p : Addr) (w₀ w₁ : BitVec 64) :
    Spec.Aes.bytesAt ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) p 16 = le8 w₀ ++ le8 w₁ := by
  have hs : Mem.Sep p (64 / 8) (p + BitVec.ofNat 64 8) (64 / 8) := by
    have := Offset.sep p (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by decide)
    simpa using this
  have h₀ : Spec.Aes.bytesAt ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) p 8 = le8 w₀ := by
    rw [← le8_readW, Mem.readW_writeW_sep hs (by decide), Mem.readW_writeW_self64]
  have h₁ : Spec.Aes.bytesAt ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) (p + BitVec.ofNat 64 8) 8 = le8 w₁ := by
    rw [← le8_readW, Mem.readW_writeW_self64]
  rw [bytesAt_split, h₀, h₁]

theorem xor_append {a b c d : List Byte} (h : a.length = c.length) :
    Spec.Cmac.xor (a ++ b) (c ++ d) = Spec.Cmac.xor a c ++ Spec.Cmac.xor b d := by
  simp [Spec.Cmac.xor, List.zipWith_append h]

/-- The XOR of two blocks, a word at a time. -/
theorem xor_words (m : Mem) (p q : Addr) :
    le8 (m.readW p 64 ^^^ m.readW q 64) ++ le8 (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64) =
      Spec.Cmac.xor (Spec.Aes.bytesAt m p 16) (Spec.Aes.bytesAt m q 16) := by
  rw [le8_xor, le8_xor, le8_readW, le8_readW, le8_readW, le8_readW, bytesAt_split m p,
    bytesAt_split m q, xor_append (by simp [Spec.Aes.bytesAt])]

end VG.Proof.Cmac
