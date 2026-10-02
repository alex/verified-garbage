import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Framework.Mem
import Mathlib.Data.List.Induction

/-!
# Blocks as bytes, and the counter blocks of `inc₃₂`

`toBytes (ofBytes bs) = bs` for 16 bytes, the bytes of a XOR of blocks, and
the bytes of `inc₃₂ⁱ(x)`: the first twelve are those of `x`, and the last
four the big-endian `x mod 2³² + i`.
-/

namespace VG.Proof.Aes

open VG VG.Spec.Gcm

/-- The value of big-endian bytes. -/
def beVal (bs : List Byte) : Nat := bs.foldl (fun acc b => 256 * acc + b.toNat) 0

theorem beVal_append (bs : List Byte) (x : Byte) : beVal (bs ++ [x]) = 256 * beVal bs + x.toNat := by
  simp [beVal, List.foldl_append]

theorem beVal_lt (bs : List Byte) : beVal bs < 256 ^ bs.length := by
  induction bs using List.reverseRecOn with
  | nil => simp [beVal]
  | append_singleton bs x ih =>
    rw [beVal_append, List.length_append, List.length_singleton, Nat.pow_succ]
    have := x.isLt
    omega

/-- Byte `k` (from the left) of big-endian bytes. -/
theorem beVal_digit (bs : List Byte) {k : Nat} (hk : k < bs.length) :
    beVal bs / 256 ^ (bs.length - 1 - k) % 256 = (bs.getD k 0).toNat := by
  induction bs using List.reverseRecOn generalizing k with
  | nil => simp at hk
  | append_singleton bs x ih =>
    rw [beVal_append]
    simp only [List.length_append, List.length_singleton] at hk ⊢
    by_cases h : k = bs.length
    · subst h
      simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.pow_zero, Nat.div_one]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
      simp; have := x.isLt; omega
    · have hk' : k < bs.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk', ← List.getD_eq_getElem?_getD,
        ← ih hk', show bs.length + 1 - 1 - k = (bs.length - 1 - k) + 1 by omega, Nat.pow_succ',
        ← Nat.div_div_eq_div_mul, Nat.mul_add_div (by decide), Nat.div_eq_of_lt x.isLt, Nat.add_zero]

theorem toBytes_getD (x : Block) {k : Nat} (hk : k < 16) :
    (toBytes x).getD k 0 = x.extractLsb' (8 * (15 - k)) 8 := by
  simp [toBytes, List.getD_eq_getElem?_getD, hk]

theorem toBytes_ofBytes {bs : List Byte} (h : bs.length = 16) {k : Nat} (hk : k < 16) :
    (toBytes (ofBytes bs)).getD k 0 = bs.getD k 0 := by
  rw [toBytes_getD _ hk]
  apply BitVec.eq_of_toNat_eq
  have hlt := beVal_lt bs
  rw [h] at hlt
  rw [BitVec.extractLsb'_toNat]
  unfold ofBytes
  rw [BitVec.toNat_ofNat]
  change (beVal bs % 2 ^ 128) >>> (8 * (15 - k)) % 2 ^ 8 = _
  rw [Nat.mod_eq_of_lt (a := beVal bs) (b := 2 ^ 128) (by simpa using hlt), Nat.shiftRight_eq_div_pow,
    show 2 ^ (8 * (15 - k)) = 256 ^ (15 - k) by rw [Nat.pow_mul],
    show (2 : Nat) ^ 8 = 256 from rfl]
  have := beVal_digit bs (k := k) (by omega)
  rw [h, show 16 - 1 - k = 15 - k by omega] at this
  exact this

theorem toBytes_xor (x y : Block) {k : Nat} (hk : k < 16) :
    (toBytes (x ^^^ y)).getD k 0 = (toBytes x).getD k 0 ^^^ (toBytes y).getD k 0 := by
  rw [toBytes_getD _ hk, toBytes_getD _ hk, toBytes_getD _ hk]
  ext t ht
  simp [BitVec.getElem_extractLsb']

theorem inc32_hi (x : Block) : (inc32 x).extractLsb' 32 96 = x.extractLsb' 32 96 := by
  ext t ht
  simp only [inc32, BitVec.getElem_extractLsb']
  rw [BitVec.getLsbD_append]
  simp [show ¬ 32 + t < 32 by omega, ht]

theorem inc32_lo (x : Block) : (inc32 x).extractLsb' 0 32 = x.extractLsb' 0 32 + 1 := by
  ext t ht
  simp only [inc32, BitVec.getElem_extractLsb']
  rw [BitVec.getLsbD_append]
  simp [ht, ← BitVec.getLsbD_eq_getElem]

theorem repeat_inc32_hi (x : Block) (i : Nat) :
    (Nat.repeat inc32 i x).extractLsb' 32 96 = x.extractLsb' 32 96 := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Nat.repeat, inc32_hi, ih]

theorem repeat_inc32_lo (x : Block) (i : Nat) :
    (Nat.repeat inc32 i x).extractLsb' 0 32 = x.extractLsb' 0 32 + BitVec.ofNat 32 i := by
  induction i with
  | zero => simp [Nat.repeat]
  | succ i ih =>
    rw [Nat.repeat, inc32_lo, ih, BitVec.add_assoc]
    congr 1
    rw [BitVec.ofNat_add]; rfl

/-- The bytes of `inc₃₂ⁱ(x)`. -/
theorem ctrBlock_byte (x : Block) (i : Nat) {k : Nat} (hk : k < 16) :
    (toBytes (Nat.repeat inc32 i x)).getD k 0 =
      if k < 12 then (toBytes x).getD k 0
      else (x.extractLsb' 0 32 + BitVec.ofNat 32 i).extractLsb' (8 * (15 - k)) 8 := by
  rw [toBytes_getD _ hk]
  split
  · rw [toBytes_getD _ hk]
    have := congrArg (BitVec.extractLsb' (8 * (15 - k) - 32) 8) (repeat_inc32_hi x i)
    ext t ht
    have h2 := congrArg (fun v => v[t]) this
    simp only [BitVec.getElem_extractLsb'] at h2 ⊢
    simp only [BitVec.getLsbD_extractLsb'] at h2
    rw [show 32 + (8 * (15 - k) - 32 + t) = 8 * (15 - k) + t by omega] at h2
    simpa [show 8 * (15 - k) - 32 + t < 96 by omega] using h2
  · rw [← repeat_inc32_lo]
    ext t ht
    simp only [BitVec.getElem_extractLsb']
    simp [show 8 * (15 - k) + t < 32 by omega]

/-- Blocks are equal if their bytes are. -/
theorem block_ext {x y : Block} (h : ∀ k < 16, (toBytes x).getD k 0 = (toBytes y).getD k 0) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have := congrArg (fun v : Byte => v.getLsbD (t % 8)) (h (15 - t / 8) (by omega))
  simp only [toBytes_getD _ (show 15 - t / 8 < 16 by omega), BitVec.getLsbD_extractLsb',
    show t % 8 < 8 by omega, decide_true, Bool.true_and] at this
  rwa [show 8 * (15 - (15 - t / 8)) + t % 8 = t by omega] at this

theorem toBytes_blockAt (m : Mem) (p : Addr) {k : Nat} (hk : k < 16) :
    (toBytes (blockAt m p)).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  rw [blockAt, toBytes_ofBytes (by simp [Spec.Aes.bytesAt]) hk]
  simp [Spec.Aes.bytesAt, List.getD_eq_getElem?_getD, hk]

/-- Bit `j` of byte `i` of the block at `p`. -/
theorem blockAt_bit (m : Mem) (p : Addr) {i j : Nat} (hi : i < 16) (hj : j < 8) :
    (blockAt m p).getLsbD (8 * (15 - i) + j) = (m (p + BitVec.ofNat 64 i)).getLsbD j := by
  rw [← toBytes_blockAt m p hi, toBytes_getD _ hi, BitVec.getLsbD_extractLsb']
  simp [hj]

/-- Counter block `i` (`inc₃₂ⁱ(icb)`), as an AES state. -/
def ctrState (icb : Block) (i : Nat) : Spec.Aes.State :=
  Vector.ofFn fun k => (toBytes (Nat.repeat inc32 i icb)).getD k 0

end VG.Proof.Aes
