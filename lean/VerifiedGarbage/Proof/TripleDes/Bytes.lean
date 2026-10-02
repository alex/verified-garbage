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


theorem blockAt_eq_of_frame {rs : List VG.Region} {m m' : VG.Mem} (p : VG.Addr)
    (hf : VG.Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : VG.Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes hd (by change 8 ≤ 2 ^ 64; decide) hi

theorem bytesAt_eq_of_frame {rs : List VG.Region} {m m' : VG.Mem} (p : VG.Addr) (n : Nat)
    (hf : VG.Frame rs m m') (hn : n ≤ 2 ^ 64)
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : VG.Region).Disjoint r) : bytesAt m' p n = bytesAt m p n := by
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  exact hf.bytes hd hn (List.mem_range.mp hi)


end VG.Proof.TripleDes
