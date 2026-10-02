import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Blake2.Stream

/-! Serialize the final word block as the same 1024 bytes consumed by H′. -/

namespace VG.Proof.Argon2

open VG VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

theorem serialize_blockAt (m : Mem) (p : Addr) : serialize (blockAt m p) = bytesAt m p 1024 := by
  have words : (blockAt m p).toList =
      (List.range 128).map (fun j => m.readW (p + BitVec.ofNat 64 (8 * j)) 64) := by
    rw [blockAt, Vector.toList_ofFn]
    apply List.ext_getElem (by simp only [List.length_ofFn, List.length_map, List.length_range])
    intro i hi _
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    rfl
  rw [serialize, words, List.flatMap_map]
  have bytes := Proof.Blake2.bytesAt_words (w := 64) m p 128
  change bytesAt m p 1024 = _ at bytes
  rw [bytes]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  exact Proof.Blake2.wordBytes_readW m _ (Or.inr rfl)

end VG.Proof.Argon2
