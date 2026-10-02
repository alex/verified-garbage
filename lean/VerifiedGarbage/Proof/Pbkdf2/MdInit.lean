import VerifiedGarbage.Proof.Pbkdf2.MdStep
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Framework.Bswap

/-!
# HMAC over a Merkle–Damgård hash function: a key's states as one compression each

HMAC's `init`, for a key of at most a block, makes each streaming state
absorb one block (`K₀ ⊕ ipad`, `K₀ ⊕ opad`): one compression of the
initial hash value. A state whose hash value is that compression, of the
block stored in its buffer, represents the block (`repr_block`), for any
hash function the streaming proofs describe (`Md`), whatever the target.
The outer block is the inner one with `ipad ⊕ opad = 0x6a` in every byte
(`xorPad_6a`), and the key of at most a block is padded with zeros
(`blockKey_short`). The blocks are written word by word: words of a byte
repeated (`writeW_rep`), and words of the inner block XORed with `0x6a`
repeated (`writeW_xorRep`), with the key's bytes over the first ones
(`bytes_over`).
-/

namespace VG.Proof.MdStream.Md

open VG.Spec.Hmac (xorPad ipad opad blockKey)
open VG.Spec.Sha256 (bytesAt)

variable {B N L : Nat} {H : Md B N L}

/-- The streaming state at `p`, whose hash value is `iv` compressed with the
block in its buffer when that held `x`, represents `x`. -/
theorem repr_block {iv : H.HV} {m m' : Mem} {p : Addr} {x : List Byte} (hB : 0 < B) (hx : x.length = B)
    (hb : bytesAt m (p + BitVec.ofNat 64 N) B = x)
    (hs : H.stateAt m' p = H.compress iv (H.blockAt m (p + BitVec.ofNat 64 N))) : H.Repr iv m' p x := by
  refine ⟨?_, ?_⟩
  · rw [hs, hx, Nat.div_self hB, compressList_one]
    refine congrArg (H.compress iv) (H.parse_congr fun k hk => ?_)
    rw [← hb, Hmac.Common.bytesAt_getD' _ _ hk]
  · rw [hx, Nat.mod_self, Nat.div_self hB, Nat.mul_one, ← hx, List.drop_length]
    rfl

end VG.Proof.MdStream.Md

namespace VG.Proof.Pbkdf2.MdInit

open VG.Spec.Hmac (xorPad ipad opad blockKey)
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep bytesAt_writeBytes_self
  extractLsb'_read)

/-! ## Words of bytes -/

/-- A word whose four bytes are `b`. -/
theorem writeW_rep (m : Mem) (a : Addr) (b : Byte) :
    m.writeW a (b ++ b ++ b ++ b) = writeBytes m a (List.replicate 4 b) :=
  Memory.writeW_bytes _ _ _ _ (by
    show [_, _, _, _] = [b, b, b, b]
    simp (disch := decide) only [BitVec.setWidth_eq, Nat.mul_zero, Nat.reduceMul, VG.extractLsb'_append_byte_lo,
      VG.extractLsb'_append_byte_hi, Nat.reduceSub, BitVec.extractLsb'_eq_self])

/-- A word read from memory, XORed with `c` repeated, is its bytes XORed with `c`. -/
theorem writeW_xorRep (m m' : Mem) (d a : Addr) (c : Byte) :
    m.writeW d (m'.readW a 32 ^^^ (c ++ c ++ c ++ c)) = writeBytes m d ((bytesAt m' a 4).map (· ^^^ c)) := by
  refine Memory.writeW_bytes _ _ _ _ ?_
  simp only [bytesAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  simp only [Function.comp, Mem.readW, BitVec.setWidth_eq]
  rw [BitVec.extractLsb'_xor, extractLsb'_read _ _ hj]
  congr 1
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [Nat.mul_zero, Nat.reduceMul, VG.extractLsb'_append_byte_lo,
      VG.extractLsb'_append_byte_hi, Nat.reduceSub, BitVec.extractLsb'_eq_self]

/-- `0x6a` in every byte. -/
theorem c6a : (0x6a6a6a6a : BitVec 32) = (0x6a : Byte) ++ (0x6a : Byte) ++ (0x6a : Byte) ++ (0x6a : Byte) := by
  decide

/-- A byte XORed with the low byte of `v`. -/
theorem xor_byte (b : Byte) (v : BitVec 32) : ((b.setWidth 32) ^^^ v).setWidth 8 = b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

/-- Bytes all `b`, with the first ones overwritten. -/
theorem bytes_over {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} {b : Byte} (hl : xs.length ≤ n) (hn : n < 2 ^ 64)
    (hm : bytesAt m q n = List.replicate n b) :
    bytesAt (writeBytes m q xs) q n = xs ++ List.replicate (n - xs.length) b := by
  have hs : Mem.Sep (q + BitVec.ofNat 64 xs.length) (n - xs.length) q xs.length := by
    have := Offset.sep q (d := xs.length) (n := n - xs.length) (e := 0) (k := xs.length) (.inr (by omega))
      (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have e := bytesAt_add (writeBytes m q xs) q xs.length (n - xs.length)
  have e' := bytesAt_add m q xs.length (n - xs.length)
  rw [show xs.length + (n - xs.length) = n by omega] at e e'
  rw [e, bytesAt_writeBytes_self _ _ _ (by omega), bytesAt_writeBytes_sep _ _ hs (by omega)]
  rw [hm] at e'
  rw [show bytesAt m (q + BitVec.ofNat 64 xs.length) (n - xs.length) = (List.replicate n b).drop xs.length by
    rw [e', List.drop_left' (bytesAt_length _ _ _)], List.drop_replicate]

/-! ## The keys -/

/-- `K₀ ⊕ ipad ⊕ 0x6a = K₀ ⊕ opad`. -/
theorem xorPad_6a (k : List Byte) : (xorPad k ipad).map (· ^^^ 0x6a) = xorPad k opad := by
  simp only [xorPad, List.map_map]
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp, BitVec.xor_assoc]
  rfl

/-- A key of at most a block, padded with zeros. -/
theorem blockKey_short (H : Spec.Hmac.HashFunction) {key : List Byte} (h : key.length ≤ H.blockSize) :
    blockKey H key = key ++ List.replicate (H.blockSize - key.length) 0 := by
  simp only [blockKey, show ¬ (H.blockSize < key.length) by omega, ↓reduceIte]

/-- The bytes of `K₀ ⊕ ipad`, for a key of `kl ≤ B` bytes: the key's
bytes XORed with `ipad`, then `ipad`. -/
theorem xorPad_short (key : List Byte) (B : Nat) :
    xorPad (key ++ List.replicate (B - key.length) 0) ipad =
      key.map (· ^^^ ipad) ++ List.replicate (B - key.length) ipad := by
  simp only [xorPad, List.map_append, List.map_replicate]
  rfl

end VG.Proof.Pbkdf2.MdInit
