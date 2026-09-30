import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Rc2.Word

/-! # RC2's little-endian block representation -/

namespace VG.Proof.Rc2

open VG

theorem read64_byte (m : Mem) (p : Addr) (i : Nat) (hi : i < 8) :
    (m.readW p 64).extractLsb' (8 * i) 8 = m (p + BitVec.ofNat 64 i) := by
  change (m.read p 8).extractLsb' (8 * i) 8 = _
  exact Mem.extractLsb'_read m p hi

theorem extractWord (x : BitVec 64) (i : Nat) :
    ((x.extractLsb' (8 * (2 * i)) 8).setWidth 16 |||
      (x.extractLsb' (8 * (2 * i + 1)) 8).setWidth 16 <<< 8) =
        (x >>> (16 * i)).setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight]
  by_cases h : j < 8
  · simp only [hj, h, decide_true, Bool.true_and, Bool.not_true,
      Bool.false_and, Bool.or_false]
    apply congrArg x.getLsbD
    omega
  · simp only [hj, h, decide_true, Bool.true_and, decide_false, Bool.false_and,
      Bool.not_false, Bool.false_or, show j - 8 < 16 by omega, show j - 8 < 8 by omega]
    apply congrArg x.getLsbD
    omega

theorem getD_ofFn {α : Type} {n : Nat} (f : Fin n → α) (i : Nat) (hi : i < n) (d : α) :
    (Vector.ofFn f).getD i d = f ⟨i, hi⟩ := by
  simp [Vector.getD, hi]

theorem getD_eq_getElem {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (d : α) :
    v.getD i d = v[i] := by
  simp [Vector.getD, hi]

theorem decode_read64 (m : Mem) (p : Addr) (i : Nat) (hi : i < 4) :
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m p)).getD i 0 =
      ((m.readW p 64) >>> (16 * i)).setWidth 16 := by
  rw [Spec.Rc2.decodeBlock, getD_ofFn _ i hi]
  change ((Spec.Rc2.blockAt m p).getD (2 * i) 0).setWidth 16 |||
    ((Spec.Rc2.blockAt m p).getD (2 * i + 1) 0).setWidth 16 <<< 8 = _
  have lo : 2 * i < 8 := by omega
  have hi' : 2 * i + 1 < 8 := by omega
  rw [Spec.Rc2.blockAt, getD_ofFn _ _ lo, getD_ofFn _ _ hi']
  rw [← read64_byte m p (2 * i) lo, ← read64_byte m p (2 * i + 1) hi']
  exact extractWord _ i

/-- Concatenation of RC2's four little-endian words. -/
def pack (v : Spec.Rc2.State) : BitVec 64 :=
  ((v.getD 3 0 ++ v.getD 2 0) ++ v.getD 1 0) ++ v.getD 0 0

theorem pack_word (v : Spec.Rc2.State) (i : Nat) (hi : i < 4) :
    ((pack v) >>> (16 * i)).setWidth 16 = v.getD i 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [pack, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with h | h | h | h <;> subst i <;>
    simp (disch := omega) only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.zero_add,
      ite_eq_left, ite_eq_right, Nat.add_sub_cancel_left]
  all_goals apply congrArg (BitVec.getLsbD _); omega

/-- Extracting a byte within a 16-bit word agrees with extracting the
same byte directly from the packed block. -/
theorem word_byte (x : BitVec 64) (i : Nat) :
    (((x >>> (16 * (i / 2))).setWidth 16) >>> (8 * (i % 2))).setWidth 8 =
      x.extractLsb' (8 * i) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  have bound : 8 * (i % 2) + j < 16 := by omega
  rw [show decide (8 * (i % 2) + j < 16) = true by simp [bound], Bool.true_and]
  congr 1; omega

theorem encode_pack (v : Spec.Rc2.State) (i : Nat) (hi : i < 8) :
    (Spec.Rc2.encodeBlock v).getD i 0 = (pack v).extractLsb' (8 * i) 8 := by
  rw [Spec.Rc2.encodeBlock, getD_ofFn _ i hi]
  rw [← pack_word v (i / 2) (by omega)]
  exact word_byte _ i

theorem blockAt_write64 (m : Mem) (p : Addr) (v : Spec.Rc2.State) :
    Spec.Rc2.blockAt (m.writeW p (pack v)) p = Spec.Rc2.encodeBlock v := by
  apply Vector.ext
  intro i hi
  have he := encode_pack v i hi
  rw [getD_eq_getElem _ i hi] at he
  rw [he]
  rw [Spec.Rc2.blockAt, Vector.getElem_ofFn]
  simp only [Mem.writeW, BitVec.setWidth_eq, Mem.write,
    Mem.sub_ofNat_toNat p (show i < 2 ^ 64 by omega), hi, ite_true]

theorem pack_eq (v : Spec.Rc2.State) : pack v =
    (((v.getD 0 0).setWidth 64 ||| ((v.getD 1 0).setWidth 64).rotateRight 48) |||
      ((v.getD 2 0).setWidth 64).rotateRight 32) |||
      ((v.getD 3 0).setWidth 64).rotateRight 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [pack, BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_rotateRight]
  have subBound (n : Nat) : j - n < 64 := by omega
  by_cases h₁ : j < 16
  · simp (disch := omega) [h₁, hj, show j < 32 by omega, show j < 48 by omega, BitVec.getLsbD_of_ge]
  · by_cases h₂ : j < 32
    · simp (disch := omega) [h₁, h₂, hj, show j < 48 by omega, subBound, BitVec.getLsbD_of_ge,
        show j - 16 < 16 by omega]
    · by_cases h₃ : j < 48
      · simp (disch := omega) [h₁, h₂, h₃, hj, subBound, BitVec.getLsbD_of_ge]
        simp (disch := omega) only [ite_eq_left, ite_eq_right]
        simp only [Nat.sub_sub, Nat.reduceAdd]
      · simp (disch := omega) [h₁, h₂, h₃, hj, subBound, BitVec.getLsbD_of_ge]
        simp (disch := omega) only [ite_eq_right]
        simp only [Nat.sub_sub, Nat.reduceAdd]

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (p : Addr)
    (hd : ∀ r ∈ rs, (Region.mk p 8).Disjoint r) :
    Spec.Rc2.blockAt m' p = Spec.Rc2.blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Rc2.blockAt, Vector.getElem_ofFn]
  exact hf.bytes hd (show 8 ≤ 2 ^ 64 by decide) hi

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (p : Addr)
    (hd : ∀ r ∈ rs, (Region.mk p 128).Disjoint r) :
    Spec.Rc2.scheduleAt m' p = Spec.Rc2.scheduleAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Rc2.scheduleAt, Vector.getElem_ofFn]
  rw [hf.bytes hd (show 128 ≤ 2 ^ 64 by decide) (show 2 * i < 128 by omega),
    hf.bytes hd (show 128 ≤ 2 ^ 64 by decide) (show 2 * i + 1 < 128 by omega)]

end VG.Proof.Rc2
