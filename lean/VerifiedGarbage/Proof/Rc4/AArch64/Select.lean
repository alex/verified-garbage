import VerifiedGarbage.Proof.Rc4.AArch64.Lookup

/-! Byte equality and replacement using baseline NEON register tables. -/
namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64

theorem toNat_cat {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-- Multiplication by 0x01010101 duplicates a byte across a word. -/
theorem pack_byte (b : Byte) :
    b.setWidth 32 * 0x01010101#32 = (b ++ b ++ b ++ b : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt,
    BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt,
    BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt]
  simp only [Nat.shiftLeft_eq, show 2 ^ 8 = 256 by decide]
  bv_omega

def repeatByte (b : Byte) : BitVec 128 := ofVBytes fun _ => b

theorem repeat_words (b : Byte) :
    ofVWords (b.setWidth 32 * 0x01010101#32) (b.setWidth 32 * 0x01010101#32)
      (b.setWidth 32 * 0x01010101#32) (b.setWidth 32 * 0x01010101#32) = repeatByte b := by
  rw [pack_byte]
  apply BitVec.eq_of_toNat_eq
  simp only [ofVWords, repeatByte, ofVBytes, toNat_cat, Nat.reducePow]
  omega

def laneIndices : BitVec 128 := ofVBytes (BitVec.ofNat 8)

def eqTable : BitVec 128 := ofVBytes fun i => if i = 0 then 255 else 0

/-- The equality table returns all ones exactly at index zero. -/
theorem eq_mask (b : Byte) :
    (if b.toNat < 16 then vbyte eqTable b.toNat else 0#8) =
      if b = 0#8 then 255 else 0 := by
  by_cases h : b.toNat < 16
  · rw [ite_eq_left h]
    unfold eqTable
    rw [vbyte_ofVBytes _ h]
    have hz : b.toNat = 0 ↔ b = 0#8 := by bv_omega
    simp only [hz]
  · rw [ite_eq_right h, ite_eq_right (show ¬ b = 0#8 by intro hb; subst b; simp at h)]
    rfl

/-- One mask byte for each position equal to `idx`. -/
theorem mask_lane (idx : Byte) (e : Nat) (he : e < 16) :
    (if (vbyte (repeatByte idx ^^^ laneIndices) e).toNat < 16 then
      vbyte eqTable (vbyte (repeatByte idx ^^^ laneIndices) e).toNat else 0#8) =
    if idx.toNat = e then 255 else 0 := by
  have hx : vbyte (repeatByte idx ^^^ laneIndices) e = idx ^^^ BitVec.ofNat 8 e := by
    simp only [vbyte, BitVec.extractLsb'_xor]
    change vbyte (repeatByte idx) e ^^^ vbyte laneIndices e = _
    unfold repeatByte laneIndices
    rw [vbyte_ofVBytes _ he, vbyte_ofVBytes _ he]
  rw [hx, eq_mask]
  have hzero : idx ^^^ BitVec.ofNat 8 e = 0#8 ↔ idx.toNat = e := by
    rw [BitVec.xor_eq_zero_iff]
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · intro h; exact BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  simp only [hzero]

def replaceVector (s : BitVec 128) (idx value : Byte) : BitVec 128 :=
  s ^^^ ((s ^^^ repeatByte value) &&& ofVBytes fun e => if idx.toNat = e then 255 else 0)

theorem replace_lane (s : BitVec 128) (idx value : Byte) (e : Nat) (he : e < 16) :
    vbyte (replaceVector s idx value) e = if idx.toNat = e then value else vbyte s e := by
  unfold replaceVector
  simp only [vbyte, BitVec.extractLsb'_xor, BitVec.extractLsb'_and]
  change vbyte s e ^^^ ((vbyte s e ^^^ vbyte (repeatByte value) e) &&&
    vbyte (ofVBytes fun k => if idx.toNat = k then 255 else 0) e) = _
  unfold repeatByte
  rw [vbyte_ofVBytes _ he, vbyte_ofVBytes _ he]
  by_cases h : idx.toNat = e
  · simp only [h, ite_true, BitVec.ofNat_eq_ofNat]
    rw [show (vbyte s e ^^^ value) &&& 255#8 = (vbyte s e ^^^ value) from BitVec.and_allOnes]
    simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp [h, vbyte]

/-- Full vector equality follows from byte equality. -/
theorem bytes_ext {x y : BitVec 128} (h : ∀ e < 16, vbyte x e = vbyte y e) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have he := congrArg (fun b : Byte => b.getLsbD (k % 8)) (h (k / 8) (by omega))
  simp only [vbyte, BitVec.getLsbD_extractLsb', show k % 8 < 8 by omega,
    decide_true, Bool.true_and, show 8 * (k / 8) + k % 8 = k by omega] at he
  exact he

/-- The actual TBL mask is the selector used by `replaceVector`. -/
theorem mask_vector (idx : Byte) :
    (ofVBytes fun e => if (vbyte (repeatByte idx ^^^ laneIndices) e).toNat < 16 then
      vbyte eqTable (vbyte (repeatByte idx ^^^ laneIndices) e).toNat else 0#8) =
    ofVBytes fun e => if idx.toNat = e then 255 else 0 := by
  apply bytes_ext
  intro e he
  rw [vbyte_ofVBytes _ he, vbyte_ofVBytes _ he, mask_lane _ _ he]

end VG.Proof.Rc4.AArch64

