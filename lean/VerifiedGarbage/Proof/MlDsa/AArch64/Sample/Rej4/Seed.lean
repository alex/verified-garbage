import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Last
import VerifiedGarbage.Proof.MlKem.Mem

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (toNat_lsl_n toNat_add_n)

def tailWord (m : Mem) (p : Addr) : BitVec 64 := lastWord m p + 0x1f0000

theorem toNat_append_add {n k : Nat} (a : BitVec n) (b : BitVec k) :
    (a++b).toNat = a.toNat * 2^k + b.toNat := by
  rw [BitVec.toNat_append,← Nat.shiftLeft_add_eq_or_of_lt b.isLt,Nat.shiftLeft_eq]

theorem tailWord_eq (m : Mem) (p : Addr) :
    tailWord m p = (((0#40 ++ 0x1f#8) ++ m (p+33)) ++ m (p+32)) := by
  have h0 := (m (p+32)).isLt
  have h1 := (m (p+33)).isLt
  have hs : (((m (p+33)).setWidth 64) <<< 8).toNat = (m (p+33)).toNat * 256 := by
    rw [toNat_lsl_n (by rw [BitVec.toNat_setWidth]; omega),BitVec.toNat_setWidth]
    omega
  apply BitVec.eq_of_toNat_eq
  unfold tailWord lastWord
  rw [toNat_add_n (by rw [BitVec.toNat_add,BitVec.toNat_setWidth,hs]; change (_ % _ + 2031616 < _); omega),
    toNat_add_n (by rw [BitVec.toNat_setWidth,hs]; omega),BitVec.toNat_setWidth,hs]
  simp only [toNat_append_add,BitVec.toNat_ofNat]
  rw [show (0x1f0000 : BitVec 64).toNat = 2031616 from rfl]
  simp only [Nat.reducePow,Nat.zero_mod,Nat.reduceMod,Nat.reduceMul,Nat.reduceAdd]
  omega

theorem tailWord_byte (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (tailWord m p).extractLsb' (8*k) 8 =
      if k = 0 then m (p+32) else if k = 1 then m (p+33) else if k = 2 then 0x1f else 0 := by
  rw [tailWord_eq]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with h | h | h | h
  · subst k
    simp only [Nat.mul_zero,BitVec.extractLsb'_append_eq_right,ite_true]
  · subst k
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    simp only [Nat.reduceMul,Nat.reduceSub,BitVec.extractLsb'_append_eq_right,
      ite_eq_right (by decide : ¬ (1:Nat) = 0),ite_true]
  · subst k
    rw [BitVec.extractLsb'_append_eq_of_le (by decide),BitVec.extractLsb'_append_eq_of_le (by decide)]
    simp only [Nat.reduceMul,Nat.reduceSub,BitVec.extractLsb'_append_eq_right,
      ite_eq_right (by decide : ¬ (2:Nat) = 0),ite_eq_right (by decide : ¬ (2:Nat) = 1),ite_true]
    rfl
  · rw [BitVec.extractLsb'_append_eq_of_le (by omega),BitVec.extractLsb'_append_eq_of_le (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega)]
    simp only [ite_eq_right (by omega : ¬ k = 0),ite_eq_right (by omega : ¬ k = 1),
      ite_eq_right (by omega : ¬ k = 2)]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp

/-- The initial state obtained by absorbing a 34-byte seed and SHAKE padding. -/
def seedState (m : Mem) (p : Addr) : Spec.Sha3.State := Vector.ofFn fun i : Fin 25 =>
  if i.val < 4 then m.readW (p+BitVec.ofNat 64 (8*i.val)) 64
  else if i.val = 4 then tailWord m p
  else if i.val = 20 then 0x8000000000000000 else 0

theorem pad_byte : ∀ k < 8, (0x8000000000000000 : BitVec 64).extractLsb' (8*k) 8 =
    if k = 7 then 0x80 else 0 := by decide

theorem seedState_get (m : Mem) (p : Addr) {i : Nat} (hi : i < 25) :
    (seedState m p)[i]! = if i < 4 then m.readW (p+BitVec.ofNat 64 (8*i)) 64
      else if i = 4 then tailWord m p else if i = 20 then 0x8000000000000000 else 0 := by
  rw [Proof.Sha3.getElem!_eq _ hi]
  unfold seedState
  rw [Vector.getElem_ofFn]

theorem seedState_eq (m : Mem) (p : Addr) :
    seedState m p = Proof.Sha3.Seed34.A0 (Spec.Sha3.bytesAt m p 34) := by
  apply Proof.Sha3.ext_bytes
  intro j hj
  rw [Proof.Sha3.Seed34.byteOf_A0 (Proof.Sha3.bytesAt_length _ _ _) hj]
  unfold Proof.Sha3.byteOf
  rw [seedState_get m p (by omega)]
  by_cases h32 : j < 32
  · rw [ite_eq_left (by omega : j/8 < 4),ite_eq_left (by omega : j < 34),
      Proof.MlKem.bytesAt_getD m p (by omega)]
    change (m.read (p+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _
    rw [Mem.extractLsb'_read m _ (by omega),BitVec.add_assoc,← BitVec.ofNat_add,
      show 8*(j/8)+j%8 = j by omega]
  · rw [ite_eq_right (by omega : ¬ j/8 < 4)]
    by_cases h40 : j < 40
    · rw [ite_eq_left (by omega : j/8 = 4),tailWord_byte m p (by omega)]
      rcases (show j = 32 ∨ j = 33 ∨ j = 34 ∨ 35 ≤ j by omega) with h | h | h | h
      · subst j
        simp only [Nat.reduceMod,ite_true]
        rw [Proof.MlKem.bytesAt_getD m p (by decide)]
        rfl
      · subst j
        simp only [Nat.reduceMod,ite_eq_right (by decide : ¬ (1:Nat) = 0),ite_true]
        rw [Proof.MlKem.bytesAt_getD m p (by decide)]
        rfl
      · subst j
        simp
      · simp (disch := omega) only [ite_eq_right]
    · rw [ite_eq_right (by omega : ¬ j/8 = 4)]
      by_cases h20 : j/8 = 20
      · rw [ite_eq_left h20,pad_byte (j%8) (by omega)]
        by_cases he : j = 167 <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
      · rw [ite_eq_right h20]
        simp (disch := omega) only [ite_eq_right]
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp
end VG.Proof.MlDsa.AArch64.Sample.Rej4
