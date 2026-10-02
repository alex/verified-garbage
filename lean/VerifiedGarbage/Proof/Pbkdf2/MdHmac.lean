import VerifiedGarbage.Proof.Pbkdf2.MdStep
import VerifiedGarbage.Proof.Hmac.Common

/-!
# HMAC over a Merkle–Damgård hash function: the outer hash as one compression

Untrusted: everything here is checked by Lean. HMAC's outer hash, of a key's
outer block (`K₀ ⊕ opad`, one block) and an inner digest of `D` bytes, is one
compression, of the hash value of the outer block with the block of the
digest and the padding of a `B + D`-byte message (`Link.hmac_outer`), for any
hash function the streaming proofs describe (`Md`), whatever the target. A
block in memory made of `D` bytes followed by that padding is the padded
block of those bytes (`blockAt_tailPad`).
-/

namespace VG.Proof.MdStream.Md

open VG.Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)
open VG.Spec.Sha256 (bytesAt)

variable {B N L : Nat} {H : Md B N L}

/-- The block in memory at `p`, of `D` bytes of message and the padding after
them. -/
theorem blockAt_tailPad {D : Nat} {m : Mem} {p : Addr} (hD : D ≤ B)
    (h : bytesAt m (p + BitVec.ofNat 64 D) (B - D) = H.tailPad D) :
    H.blockAt m p = H.tailBlock D (bytesAt m p D) := by
  simp only [blockAt, tailBlock]
  refine H.parse_congr fun k hk => ?_
  have e := Hmac.Common.bytesAt_add m p D (B - D)
  rw [h, show D + (B - D) = B by omega] at e
  rw [← e, Hmac.Common.bytesAt_getD' _ _ hk]

/-- The hash of a block `p` and `D` bytes `x` is one compression, of the hash
value of `p` with the block of `x` and the padding. -/
theorem Link.hash_outer {S : StreamingHash} {iv : H.HV} {D : Nat} (hl : H.Link S iv D) {p x : List Byte}
    (hp : p.length = B) (hx : x.length = D) :
    S.H.hash (p ++ x) = (H.digest (H.compress (H.compressList iv p 1) (H.tailBlock D x))).take D := by
  rw [hl.hash, Md.hash_block H iv hp hx hl.DL]

/-- A digest has `D` bytes. -/
theorem Link.hash_length {S : StreamingHash} {iv : H.HV} {D : Nat} (hl : H.Link S iv D) (x : List Byte) :
    (S.H.hash x).length = D := by
  rw [hl.hash, List.length_take, Md.hash, H.digest_length]; exact Nat.min_eq_left hl.DN

/-- HMAC's outer hash, for a key of one block, is one compression of the hash
value of its outer block, with the inner digest padded. -/
theorem Link.hmac_outer {S : StreamingHash} {iv : H.HV} {D : Nat} (hl : H.Link S iv D) {k0 : List Byte}
    (hk : k0.length = B) (text : List Byte) :
    hmacBlockKey S.H k0 text = (H.digest (H.compress (H.compressList iv (xorPad k0 opad) 1)
      (H.tailBlock D (S.H.hash (xorPad k0 ipad ++ text))))).take D :=
  hl.hash_outer (by simp [xorPad, hk]) (hl.hash_length _)

end VG.Proof.MdStream.Md
