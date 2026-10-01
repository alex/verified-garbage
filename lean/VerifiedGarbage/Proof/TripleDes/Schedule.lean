import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.TripleDes

open VG VG.Spec.TripleDes

theorem reverse_or8 (a b c d e f g h : BitVec 64) :
    a ||| b ||| c ||| d ||| e ||| f ||| g ||| h =
      h ||| g ||| f ||| e ||| d ||| c ||| b ||| a := by ac_rfl

theorem littleEndian_word (b : Nat → Byte) :
    (List.range 8).foldl (fun out j => out ||| ((b j).zeroExtend 64 <<< (8 * j))) (0 : BitVec 64) =
      (b 7 ++ b 6 ++ b 5 ++ b 4 ++ b 3 ++ b 2 ++ b 1 ++ b 0 : BitVec 64).setWidth 64 := by
  simp only [List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons,
    List.foldl_nil, List.nil_append, Nat.reduceAdd, Nat.reduceMul, BitVec.shiftLeft_zero]
  rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or,
    BitVec.setWidth_append_eq_shiftLeft_setWidth_or]
  have hz : (0 : BitVec 64) ||| (b 0).zeroExtend 64 = (b 0).zeroExtend 64 := BitVec.zero_or
  rw [hz]
  simp only [BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, Nat.reduceAdd]
  exact reverse_or8 _ _ _ _ _ _ _ _


theorem readW64_cat (m : Mem) (p : Addr) :
    m.readW p 64 = (m (p + BitVec.ofNat 64 7) ++ m (p + BitVec.ofNat 64 6) ++
      m (p + BitVec.ofNat 64 5) ++ m (p + BitVec.ofNat 64 4) ++ m (p + BitVec.ofNat 64 3) ++
      m (p + BitVec.ofNat 64 2) ++ m (p + BitVec.ofNat 64 1) ++ m p : BitVec 64).setWidth 64 := by
  simp only [Mem.readW, Mem.read, BitVec.add_assoc]
  rw [BitVec.zero_width_append]
  rfl

theorem scheduleAt_readW (m : Mem) (p : Addr) (i : Nat) (hi : i < 48) :
    (scheduleAt m p)[i] = m.readW (p + BitVec.ofNat 64 (8 * i)) 64 := by
  have h := littleEndian_word (fun j => m (p + BitVec.ofNat 64 (8 * i + j)))
  have hread := readW64_cat m (p + BitVec.ofNat 64 (8 * i))
  rw [Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat,
    Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat,
    Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat,
    Offset.add_ofNat_add_ofNat] at hread
  simp only [scheduleAt, Vector.getElem_ofFn]
  exact h.trans hread.symm


theorem vector_getD {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (fallback : α) :
    v.getD i fallback = v[i]'hi :=
  (Array.getElem_eq_getD fallback).symm

theorem componentSchedule_readW (m : Mem) (p : Addr) (c j : Nat) (hc : c < 3) (hj : j < 16) :
    (componentSchedule (scheduleAt m p) c).getD j 0 =
      (m.readW (p + BitVec.ofNat 64 (8 * (16 * c + j))) 64).setWidth 48 := by
  rw [vector_getD _ j hj 0]
  simp only [componentSchedule, Vector.getElem_ofFn]
  rw [vector_getD _ (16 * c + j) (by omega) 0, scheduleAt_readW m p _ (by omega)]

theorem scheduleAt_eq_of_frame {rs : List Region} {m m' : Mem} (p : Addr)
    (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p, 384⟩ : Region).Disjoint r) : scheduleAt m' p = scheduleAt m p := by
  apply Vector.ext
  intro i hi
  rw [scheduleAt_readW m' p i hi, scheduleAt_readW m p i hi]
  exact hf.readW (r := ⟨p, 384⟩)
    (Offset.contains_base p (by omega) (by omega)) hd (by decide)


end VG.Proof.TripleDes
