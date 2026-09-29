import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Sha512.Stream

/-!
# The SHA-512 family as a streaming Merkle–Damgård hash function

Untrusted: everything here is checked by Lean. SHA-512 (for any initial hash
value, so SHA-384, SHA-512/224 and SHA-512/256 too) as an instance of
`Proof.MdStream.Md`, for the generic streaming proofs: its `Repr` and
`finalHash` are the generic ones, by unfolding.
-/

namespace VG.Proof.Sha512

open Spec.Sha512

/-- The big-endian bytes of a 128-bit word (§5.1.2). -/
def lenField (x : BitVec 128) : List Byte := (List.range 16).reverse.map fun i => x.extractLsb' (8 * i) 8

/-- The SHA-512 family: 128-byte blocks, a 64-byte hash value, the
big-endian 128-bit bit count as its length field (for messages shorter than
2⁶⁴ bytes, which the count modulo 2⁶⁴ determines), and all the words of the
hash value big-endian as its output (which the truncated variants
truncate). -/
def md : MdStream.Md 128 64 16 where
  HV := HashValue
  Blk := Block
  stateAt := stateAt
  parse := parseBlock
  compress := compress
  lenBytes n := lenField (BitVec.ofNat 128 (8 * n))
  lenOf x := lenField (BitVec.ofNat 128 (8 * x.toNat))
  lenOk n := n < 2 ^ 64
  digest h := h.toList.flatMap wordBytes
  stateAt_congr := Stream.stateAt_congr
  parse_congr := Stream.parseBlock_congr
  lenBytes_length _ := by simp [lenField]
  lenOf_eq n h := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  lenOf_length _ := by simp [lenField]
  digest_length h := by simp [List.length_flatMap, wordBytes, List.map_const']

/-- The 128-bit length in bits of a 64-bit count of bytes is the 64-bit
words `count >> 61` and `8 count mod 2⁶⁴`, big-endian. -/
theorem lenOf_split (x : BitVec 64) :
    md.lenOf x = wordBytes (x >>> 61) ++ wordBytes (BitVec.ofNat 64 (8 * x.toNat)) := by
  have hx := x.isLt
  simp only [md, lenField, wordBytes, List.range_succ, List.range_zero, List.nil_append,
    List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow] at * <;> omega

theorem repr_iff {iv : HashValue} {mem : Mem} {p : Addr} {m : List Byte} :
    Repr iv mem p m ↔ md.Repr iv mem p m := Iff.rfl

theorem finalHash_eq (iv : HashValue) (m : List Byte) : finalHash iv m = md.hash iv m := rfl

end VG.Proof.Sha512
