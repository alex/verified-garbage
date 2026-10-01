import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.Framework.Mem

namespace VG.Proof.TripleDes

open VG.Spec.TripleDes

def catBlock (b : Block) : BitVec 64 :=
  b[0] ++ b[1] ++ b[2] ++ b[3] ++ b[4] ++ b[5] ++ b[6] ++ b[7]

theorem block_list (b : Block) : b.toList = List.ofFn (fun i : Fin 8 => b[i.val]) := by
  simpa only [Vector.toList_ofFn] using
    (congrArg (fun v : Block => v.toList) (Vector.ofFn_getElem (xs := b))).symm

theorem decodeBlock_cat (b : Block) : decodeBlock b = catBlock b := by
  unfold decodeBlock
  rw [block_list]
  simp only [List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil]
  have h : (catBlock b).setWidth 64 = catBlock b := by simp
  rw [← h]
  simp only [catBlock, BitVec.setWidth_append_eq_shiftLeft_setWidth_or]
  simp
  rfl

end VG.Proof.TripleDes
