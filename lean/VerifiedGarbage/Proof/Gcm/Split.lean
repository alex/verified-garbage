import VerifiedGarbage.Proof.Gcm.Ctr

/-!
# GCM: counter mode and GHASH of whole blocks, split

Untrusted: everything here is checked by Lean. Counter mode over two runs of
blocks is counter mode over the first, then over the second from the counter
block after the first (`ctr32_append`); the blocks at an address split the
same way (`blocksAt_add`).
-/

namespace VG.Proof.Gcm

open VG VG.Spec.Gcm

theorem keystream_add (ciph : Block → Block) (icb : Block) (a b : Nat) :
    keystream ciph icb (a + b) = keystream ciph icb a ++ keystream ciph (Nat.repeat inc32 a icb) b := by
  simp only [keystream, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, Nat.add_comm a i, repeat_add]

theorem ctr32_append (ciph : Block → Block) (icb : Block) (xs ys : List Block) :
    ctr32 ciph icb (xs ++ ys) = ctr32 ciph icb xs ++ ctr32 ciph (Nat.repeat inc32 xs.length icb) ys := by
  simp only [ctr32, List.length_append, keystream_add]
  exact List.zipWith_append (by simp [keystream])

theorem blocksAt_add (m : Mem) (p : Addr) (a b : Nat) :
    blocksAt m p (a + b) = blocksAt m p a ++ blocksAt m (p + BitVec.ofNat 64 (16 * a)) b := by
  simp only [blocksAt, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, BitVec.add_assoc, Nat.mul_add, BitVec.ofNat_add]

end VG.Proof.Gcm
