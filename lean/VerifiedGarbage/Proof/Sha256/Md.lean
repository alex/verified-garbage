import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# SHA-256 as a streaming Merkle–Damgård hash function

Untrusted: everything here is checked by Lean. SHA-256 as an instance of
`Proof.MdStream.Md`, for the generic streaming proofs: its `Repr` and `hash`
are the generic ones for `H0`, by unfolding.
-/

namespace VG.Proof.Sha256

open Spec.Sha256

/-- The big-endian bytes of a 64-bit word (§5.1.1). -/
def lenField (x : BitVec 64) : List Byte := (List.range 8).reverse.map fun i => x.extractLsb' (8 * i) 8

/-- SHA-256: 64-byte blocks, a 32-byte hash value, the big-endian 64-bit
bit count as its length field (for messages shorter than 2⁶⁴ bits, which is
the count modulo 2⁶⁴), and the words of the hash value big-endian as its
digest. -/
def md : MdStream.Md 64 32 8 where
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

theorem hash_eq (m : List Byte) : Spec.Sha256.hash m = md.hash H0 m := rfl

end VG.Proof.Sha256
