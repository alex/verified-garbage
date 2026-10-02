import VerifiedGarbage.Proof.Pbkdf2.MdStep
import VerifiedGarbage.Proof.Hmac.Generic.Common

/-!
# HMAC's `init` over a Merkle–Damgård hash function: the padded keys

HMAC's `init` on x86-64 and AArch64 (`Impl/Pbkdf2/Md/`) writes `K₀ ⊕ ipad`
into the inner state's buffer and `K₀ ⊕ opad` into the outer one's, then
compresses each state's buffer into the initial hash value `init` set. What
it writes, and what the states then represent, are facts about memory alone,
shared by both targets:

* the inner buffer is first `ipad` in every byte, written a word at a time
  (`fill_mem`), then the key's bytes are XORed in one at a time: after `j`
  of them it holds `ipadBlk … j` (`ipadBlk_succ`), and after all of them
  `K₀ ⊕ ipad` (`ipadBlk_eq`);
* the outer buffer is the inner one XORed with `ipad ⊕ opad`, a word at a
  time (`xorOpad_mem`), which is `K₀ ⊕ opad` (`xorOpad_ipad`);
* a state whose hash value is the initial one, compressed with the block in
  its buffer, represents that block (`Md.repr_of_block`).
-/

namespace VG.Proof.Pbkdf2.MdKeys

open VG.WriteBytes (writeBytes writeBytes_append writeW8_apply write_eq_writeBytes)
open VG.Proof.Hmac.Common (bytesAt_add bytesAt_length bytesAt_writeBytes_sep extractLsb'_read)
open VG.Proof.Hmac.Generic.Common (K0 K0_length K0_lt K0_ge)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad)

/-! ## The inner buffer -/

/-- The inner buffer after the first `j` bytes of the key at `K` (in memory
`m`): those bytes, then zeros, XORed with `ipad`. -/
def ipadBlk (m : Mem) (K : Addr) (B j : Nat) : List Byte :=
  (List.range B).map fun i => (if i < j then m (K + BitVec.ofNat 64 i) else 0) ^^^ ipad

theorem ipadBlk_length (m : Mem) (K : Addr) (B j : Nat) : (ipadBlk m K B j).length = B := by
  simp [ipadBlk]

/-- Before the key: `ipad` in every byte. -/
theorem ipadBlk_zero (m : Mem) (K : Addr) (B : Nat) : ipadBlk m K B 0 = List.replicate B ipad := by
  apply List.ext_getElem (by simp [ipadBlk])
  intro i h₁ h₂
  simp [ipadBlk]

/-- One more byte of the key. -/
theorem ipadBlk_succ (m : Mem) (K : Addr) {B j : Nat} :
    (ipadBlk m K B j).set j (m (K + BitVec.ofNat 64 j) ^^^ ipad) = ipadBlk m K B (j + 1) := by
  apply List.ext_getElem (by simp [ipadBlk])
  intro i h₁ h₂
  simp only [List.getElem_set, ipadBlk, List.getElem_map, List.getElem_range]
  by_cases hij : j = i
  · subst hij; simp
  · by_cases hi : i < j
    · simp only [hij, hi, show i < j + 1 by omega, ↓reduceIte]
    · simp only [hij, hi, show ¬ i < j + 1 by omega, ↓reduceIte]

/-- After the whole key: `K₀ ⊕ ipad`. -/
theorem ipadBlk_eq (m : Mem) (K : Addr) {kl B : Nat} (h : kl ≤ B) :
    ipadBlk m K B kl = xorPad (K0 m K kl B) ipad := by
  apply List.ext_getElem (by simp [ipadBlk, xorPad, K0_length _ _ h])
  intro i h₁ h₂
  simp only [ipadBlk, xorPad, List.getElem_map, List.getElem_range]
  by_cases hi : i < kl
  · simp only [hi, ↓reduceIte, K0_lt hi]
  · simp only [hi, ↓reduceIte, K0_ge (Nat.le_of_not_lt hi)]

/-- A byte written into bytes written before. -/
theorem writeBytes_set (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < xs.length)
    (hl : xs.length < 2 ^ 64) (b : Byte) :
    (writeBytes m q xs).writeW (q + BitVec.ofNat 64 i) b = writeBytes m q (xs.set i b) := by
  funext a
  rw [writeW8_apply]
  simp only [writeBytes, List.length_set]
  by_cases ha : a = q + BitVec.ofNat 64 i
  · subst ha
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hi, List.getD_eq_getElem?_getD]
  · have hne : (a - q).toNat ≠ i := by
      intro h'
      apply ha
      have : a - q = BitVec.ofNat 64 i :=
        BitVec.eq_of_toNat_eq (by rw [h', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
      rw [← BitVec.sub_add_cancel a q, this, BitVec.add_comm]
    simp only [ha, ↓reduceIte]
    split
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne)]
    · rfl

/-- One more word of `ipad`, after `4 n` bytes of it. -/
theorem fill_mem (m : Mem) (q : Addr) (n : Nat) (h : 4 * n + 4 < 2 ^ 64) :
    (writeBytes m q (List.replicate (4 * n) ipad)).writeW (q + BitVec.ofNat 64 (4 * n)) (0x36363636 : BitVec 32) =
      writeBytes m q (List.replicate (4 * n + 4) ipad) := by
  have e : ∀ m' : Mem, m'.writeW (q + BitVec.ofNat 64 (4 * n)) (0x36363636 : BitVec 32) =
      writeBytes m' (q + BitVec.ofNat 64 (4 * n)) [ipad, ipad, ipad, ipad] := fun m' => by
    rw [Mem.writeW, write_eq_writeBytes]; rfl
  have a := writeBytes_append m q (List.replicate (4 * n) ipad) [ipad, ipad, ipad, ipad] (by simp; omega)
  rw [List.length_replicate] at a
  rw [e, a, show [ipad, ipad, ipad, ipad] = List.replicate 4 ipad from rfl, List.replicate_append_replicate]

/-! ## The outer buffer -/

/-- A word of `K₀ ⊕ ipad` XORed with `ipad ⊕ opad`. -/
theorem writeW_xorOpad (m m' : Mem) (d a : Addr) :
    m.writeW d (m'.readW a 32 ^^^ 0x6a6a6a6a) = writeBytes m d ((bytesAt m' a 4).map (· ^^^ 0x6a)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (32 : Nat) / 8 = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁]
  congr 1
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide

/-- One more word of the outer buffer, after `4 n` bytes, from the inner
buffer at `A` to the outer one at `Q`. -/
theorem xorOpad_mem (m : Mem) (A Q : Addr) (n : Nat) (hsep : Mem.Sep A (4 * n + 4) Q (4 * n + 4))
    (hlt : 4 * n + 4 < 2 ^ 64) :
    (writeBytes m Q ((bytesAt m A (4 * n)).map (· ^^^ 0x6a))).writeW (Q + BitVec.ofNat 64 (4 * n))
      ((writeBytes m Q ((bytesAt m A (4 * n)).map (· ^^^ 0x6a))).readW (A + BitVec.ofNat 64 (4 * n)) 32 ^^^
        0x6a6a6a6a) =
      writeBytes m Q ((bytesAt m A (4 * n + 4)).map (· ^^^ 0x6a)) := by
  have hl : ((bytesAt m A (4 * n)).map (· ^^^ (0x6a : Byte))).length = 4 * n := by simp [bytesAt]
  rw [writeW_xorOpad, bytesAt_writeBytes_sep]
  · rw [bytesAt_add, List.map_append]
    have := writeBytes_append m Q ((bytesAt m A (4 * n)).map (· ^^^ (0x6a : Byte)))
      ((bytesAt m (A + BitVec.ofNat 64 (4 * n)) 4).map (· ^^^ 0x6a)) (by simp [bytesAt]; omega)
    rw [hl] at this
    exact this
  · intro x hx hy
    rw [hl] at hy
    apply hsep x _ (by omega)
    rw [show x - A = (x - (A + BitVec.ofNat 64 (4 * n))) + BitVec.ofNat 64 (4 * n) by
        rw [← BitVec.sub_sub, BitVec.sub_add_cancel],
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * n) (by omega)]
    have := Nat.mod_le ((x - (A + BitVec.ofNat 64 (4 * n))).toNat + 4 * n) (2 ^ 64)
    omega
  · omega

/-- `K₀ ⊕ ipad` XORed with `ipad ⊕ opad` is `K₀ ⊕ opad`. -/
theorem xorOpad_ipad (k : List Byte) : (xorPad k ipad).map (· ^^^ 0x6a) = xorPad k opad := by
  simp only [xorPad, List.map_map]
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp_apply, ipad, opad, BitVec.xor_assoc]
  rfl

end VG.Proof.Pbkdf2.MdKeys

namespace VG.Proof.MdStream.Md

open VG.Proof.Hmac.Common (bytesAt_getD')
open Spec.Sha256 (bytesAt)

variable {B N L : Nat} (H : Md B N L)

/-- A state whose hash value is `iv`, compressed with the `B` bytes `xs` of
its buffer, represents `xs`. -/
theorem repr_of_block {iv : H.HV} {m m' : Mem} {p : Addr} {xs : List Byte} (hB : 0 < B)
    (hx : xs.length = B) (h0 : H.stateAt m p = iv) (hb : bytesAt m (p + BitVec.ofNat 64 N) B = xs)
    (hs : H.stateAt m' p = H.compress (H.stateAt m p) (H.blockAt m (p + BitVec.ofNat 64 N))) :
    H.Repr iv m' p xs := by
  refine ⟨?_, ?_⟩
  · rw [hs, h0, hx, Nat.div_self hB, H.compressList_one]
    refine congrArg (H.compress iv) (H.parse_congr fun k hk => ?_)
    rw [← hb, bytesAt_getD' _ _ hk]
  · rw [hx, Nat.mod_self, Nat.div_self hB, Nat.mul_one]
    simp only [bytesAt, List.range_zero, List.map_nil]
    exact (List.drop_eq_nil_of_le (by omega)).symm

end VG.Proof.MdStream.Md
