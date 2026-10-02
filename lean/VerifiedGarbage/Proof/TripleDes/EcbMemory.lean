import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.TripleDes

open VG

theorem blocksAt_cons (m : Mem) (p : Addr) (n : Nat) :
    Spec.TripleDes.blocksAt m p (n + 1) = Spec.TripleDes.blockAt m p :: Spec.TripleDes.blocksAt m (p + 8) n := by
  rw [Spec.TripleDes.blocksAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro i _
  apply congrArg (Spec.TripleDes.blockAt m)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (fun j => p + BitVec.ofNat 64 j) (by omega)

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (p : Addr) (n : Nat)
    (hd : ∀ r ∈ rs, (Region.mk p (8 * n)).Disjoint r) :
    Spec.TripleDes.blocksAt m' p n = Spec.TripleDes.blocksAt m p n := by
  unfold Spec.TripleDes.blocksAt
  apply List.map_congr_left
  intro i hi
  apply blockAt_eq_of_frame _ hf
  intro r hr
  exact (hd r hr).sub_left (Offset.sub_base p (by
    have h := List.mem_range.mp hi
    omega))

end VG.Proof.TripleDes
