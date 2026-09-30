import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Framework.Offset

/-! # CBC block copying, XOR, and consecutive-block memory layouts -/

namespace VG.Proof.Rc2

open VG

def wordBlock (x : BitVec 64) : Spec.Rc2.Block := Vector.ofFn fun i => x.extractLsb' (8 * i.val) 8

theorem blockAt_read64 (m : Mem) (p : Addr) : Spec.Rc2.blockAt m p = wordBlock (m.readW p 64) := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Rc2.blockAt, wordBlock, Vector.getElem_ofFn]
  exact (read64_byte m p i hi).symm

theorem wordBlock_xor (x y : BitVec 64) :
    wordBlock (x ^^^ y) = Spec.Rc2.xorBlock (wordBlock x) (wordBlock y) := by
  apply Vector.ext
  intro i hi
  simp only [wordBlock, Spec.Rc2.xorBlock, Vector.getElem_ofFn, Fin.getElem_fin, BitVec.extractLsb'_xor]

theorem blockAt_store64 (m : Mem) (p : Addr) (x : BitVec 64) :
    Spec.Rc2.blockAt (m.writeW p x) p = wordBlock x := by
  rw [blockAt_read64, Mem.readW_writeW_self64]

theorem frame_store64 (m : Mem) (p : Addr) (x : BitVec 64) :
    Frame [⟨p, 8⟩] m (m.writeW p x) :=
  (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)

theorem blockAt_copy (m : Mem) (dst src : Addr) :
    Spec.Rc2.blockAt (m.writeW dst (m.readW src 64)) dst = Spec.Rc2.blockAt m src := by
  rw [blockAt_store64, blockAt_read64 m src]

theorem blockAt_xor (m : Mem) (dst iv : Addr) :
    Spec.Rc2.blockAt (m.writeW dst (m.readW dst 64 ^^^ m.readW iv 64)) dst =
      Spec.Rc2.xorBlock (Spec.Rc2.blockAt m dst) (Spec.Rc2.blockAt m iv) := by
  rw [blockAt_store64, wordBlock_xor, blockAt_read64 m dst, blockAt_read64 m iv]

theorem blocksAt_cons (m : Mem) (p : Addr) (n : Nat) :
    Spec.Rc2.blocksAt m p (n + 1) = Spec.Rc2.blockAt m p :: Spec.Rc2.blocksAt m (p + 8) n := by
  rw [Spec.Rc2.blocksAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro i _
  apply congrArg (Spec.Rc2.blockAt m)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (fun j => p + BitVec.ofNat 64 j) (by omega)

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (p : Addr) (n : Nat)
    (hd : ∀ r ∈ rs, (Region.mk p (8 * n)).Disjoint r) :
    Spec.Rc2.blocksAt m' p n = Spec.Rc2.blocksAt m p n := by
  unfold Spec.Rc2.blocksAt
  apply List.map_congr_left
  intro i hi
  apply blockAt_frame hf
  intro r hr
  exact (hd r hr).sub_left (Offset.sub_base p (by
    have h := List.mem_range.mp hi
    omega))

end VG.Proof.Rc2
