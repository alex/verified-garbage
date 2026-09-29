import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Md5.Stream

/-!
# MD5 as a streaming Merkle–Damgård hash function

Untrusted: everything here is checked by Lean. MD5 as an instance of
`Proof.MdStream.Md`, for the generic streaming proofs: its `Repr` and `hash`
are the generic ones for `H0`, by unfolding.
-/

namespace VG.Proof.Md5

open Spec.Md5

/-- The little-endian bytes of a 64-bit word (§3.2). -/
def lenField (x : BitVec 64) : List Byte := (List.range 8).map fun i => x.extractLsb' (8 * i) 8

/-- MD5: 64-byte blocks, a 16-byte MD buffer, the little-endian 64-bit
bit count modulo 2⁶⁴ as its length field, and the words of the MD buffer
low-order byte first as its digest. -/
def md : MdStream.Md 64 16 8 where
  HV := HashValue
  Blk := Block
  stateAt := stateAt
  parse := parseBlock
  compress := compress
  lenBytes n := lenField (BitVec.ofNat 64 (8 * n))
  lenOf x := lenField (BitVec.ofNat 64 (8 * x.toNat))
  lenOk _ := True
  digest h := h.toList.flatMap wordBytes
  stateAt_congr := Stream.stateAt_congr
  parse_congr := Stream.parseBlock_congr
  lenBytes_length _ := by simp [lenField]
  lenOf_eq n _ := by
    refine congrArg lenField (BitVec.eq_of_toNat_eq ?_)
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  lenOf_length _ := by simp [lenField]
  digest_length h := by simp [List.length_flatMap, wordBytes, List.map_const']

theorem repr_iff {mem : Mem} {p : Addr} {m : List Byte} : Repr mem p m ↔ md.Repr H0 mem p m := Iff.rfl

theorem hash_eq (m : List Byte) : Spec.Md5.hash m = md.hash H0 m := rfl

/-- The digest, as 32-bit words. -/
theorem digest_eq (mem : Mem) (p : Addr) :
    md.digest (md.stateAt mem p) = (List.range 4).flatMap fun k =>
      MdStream.bytes32 false (mem.readW (p + BitVec.ofNat 64 (4 * k)) 32) := by
  simp [md, stateAt, Vector.toList_ofFn, List.range_succ, List.ofFn_succ, MdStream.bytes32, wordBytes]

end VG.Proof.Md5
