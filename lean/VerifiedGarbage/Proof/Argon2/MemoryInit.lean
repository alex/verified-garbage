import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Blake2.Stream

/-! # The RFC initialization blocks as byte strings in memory -/

namespace VG.Proof.Argon2

open VG VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

/-- A complete byte representation parses to the block at the same address. -/
theorem parseBlock_bytesAt (m : Mem) (p : Addr) : parseBlock (bytesAt m p 1024) = blockAt m p := by
  apply Vector.ext
  intro j hj
  simp only [parseBlock, blockAt, Vector.getElem_ofFn, Spec.Blake2.leWord,
    Proof.Blake2.read_eq_leBytes, BitVec.setWidth_eq]
  apply Proof.Blake2.leBytes_congr
  intro k hk
  have bound : 8 * j + k < 1024 := by omega
  simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range bound, Option.map_some, Option.getD_some,
    BitVec.ofNat_add, BitVec.add_assoc]

/-- Initialization contains one 1024-byte H′ result at each leading cell. -/
def initialBytes (h0 : List Byte) (lane column : Nat) : List Byte :=
  hPrime 1024 (h0 ++ le32 column ++ le32 lane)

/-- The byte-level call result is sufficient for the word-level matrix spec. -/
theorem blockAt_of_initialBytes (m : Mem) (p : Addr) (h0 : List Byte)
    (lane column : Nat) (h : bytesAt m p 1024 = initialBytes h0 lane column) :
    blockAt m p = parseBlock (initialBytes h0 lane column) := by
  rw [← parseBlock_bytesAt, h]

theorem initMemory_size (p : Params) (h0 : List Byte) :
    (initMemory p h0).memory.size = p.blocks := by
  simp only [initMemory, Array.size_map, List.size_toArray, List.length_range]

theorem initMemory_cell (p : Params) (h0 : List Byte) (k : Nat) (hk : k < p.blocks) :
    (initMemory p h0).memory[k]'(by rw [initMemory_size]; exact hk) =
      if k % p.laneLen < 2 then
        parseBlock (initialBytes h0 (k / p.laneLen) (k % p.laneLen))
      else zeroBlock := by
  simp only [initMemory, Array.getElem_map, List.getElem_toArray, List.getElem_range,
    initialBytes]

end VG.Proof.Argon2
