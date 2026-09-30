import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Sha1.Spec
import VerifiedGarbage.Impl.Sha1.AArch64.Sha2

/-! SHA-1's specification as computed by the AArch64 SHA instructions. -/

namespace VG.Proof.Sha1.AArch64.Sha2

open VG.AArch64 VG.Impl.Sha1.AArch64.Sha2
open VG.Spec.Sha1 (HashValue Word Block K W f)

def abcd (v : HashValue) : BitVec 128 := ofVWords v[0] v[1] v[2] v[3]
def eReg (v : HashValue) : BitVec 128 := v[4].setWidth 128

def quad (M : Block) (i : Nat) : BitVec 128 :=
  ofVWords (W M (4 * i)) (W M (4 * i + 1)) (W M (4 * i + 2)) (W M (4 * i + 3))

def hw (g : Sha1Op) (v : HashValue) (k w : Word) : HashValue :=
  #v[v[4] + v[0].rotateLeft 5 + g.f v[1] v[2] v[3] + (k + w),
     v[0], v[1].rotateLeft 30, v[2], v[3]]

theorem step_eq (g : Sha1Op) (v : HashValue) (k w : Word) :
    sha1Step g.f (k + w) (v[4], abcd v) = ((hw g v k w)[4], abcd (hw g v k w)) := by
  simp only [sha1Step, abcd, hw, vword_ofVWords_0, vword_ofVWords_1,
    vword_ofVWords_2, vword_ofVWords_3]
  rfl

def hw4 (g : Sha1Op) (v : HashValue) (k w0 w1 w2 w3 : Word) : HashValue :=
  hw g (hw g (hw g (hw g v k w0) k w1) k w2) k w3

theorem hw4_e (g : Sha1Op) (v : HashValue) (k w0 w1 w2 w3 : Word) :
    (hw4 g v k w0 w1 w2 w3)[4] = v[0].rotateLeft 30 := rfl

theorem hash_eq (g : Sha1Op) (v : HashValue) (k w0 w1 w2 w3 : Word) :
    sha1Hash g.f (abcd v) v[4] (ofVWords (k + w0) (k + w1) (k + w2) (k + w3)) =
      abcd (hw4 g v k w0 w1 w2 w3) := by
  simp only [sha1Hash, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2, vword_ofVWords_3,
    step_eq, hw4]

theorem choose_eq (x y z : Word) : shaChoose x y z = Spec.Sha1.ch x y z := (ch_eq x y z).symm

theorem majority_eq (x y z : Word) : shaMajority x y z = Spec.Sha1.maj x y z := by
  rw [maj_eq, BitVec.or_comm]; rfl

theorem f_group (i j : Nat) (hj : j < 4) : f (4 * i + j) = (op i).f := by
  funext x y z
  unfold f op
  split_ifs <;> first | omega | rfl | exact (choose_eq x y z).symm | exact (majority_eq x y z).symm

theorem k_group (i j : Nat) (hj : j < 4) : K (4 * i + j) = K (4 * i) := by
  unfold K
  split_ifs <;> first | omega | rfl

theorem round_hw (M : Block) (v : HashValue) (i j : Nat) (hj : j < 4) :
    Spec.Sha1.round M v (4 * i + j) = hw (op i) v (K (4 * i)) (W M (4 * i + j)) := by
  rw [round_eq, f_group i j hj, k_group i j hj]
  simp only [roundKW, hw]
  congr 2
  ac_rfl

theorem add_abcd (v H : HashValue) :
    VArr.s4.map2 (fun _ x y => x + y) (abcd v) (abcd H) = abcd (Vector.zipWith (· + ·) v H) := by
  simp only [VArr.map2, abcd, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2,
    vword_ofVWords_3, Vector.getElem_zipWith]


/-- Word views distribute over vector XOR. -/
theorem vword_xor (x y : BitVec 128) (e : Nat) :
    vword (x ^^^ y) e = vword x e ^^^ vword y e := by
  ext i hi
  simp only [vword, BitVec.getElem_extractLsb', BitVec.getLsbD_xor, BitVec.getElem_xor]

theorem vword_shr32 (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (x >>> 32) e = if e < 3 then vword x (e + 1) else 0 := by
  by_cases h : e < 3
  · simp only [h, ite_true]
    ext i hi
    simp only [vword, BitVec.getElem_extractLsb', BitVec.getLsbD_ushiftRight]
    congr 1; omega
  · simp only [h, ite_false]
    ext i hi
    simp only [vword, BitVec.getElem_extractLsb', BitVec.getLsbD_ushiftRight]
    rw [BitVec.getLsbD_of_ge _ _ (by omega)]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.getElem_zero]

theorem su0_words (a b c : BitVec 128) :
    sha1Su0 a b c = ofVWords
      (vword a 2 ^^^ vword a 0 ^^^ vword c 0)
      (vword a 3 ^^^ vword a 1 ^^^ vword c 1)
      (vword b 0 ^^^ vword a 2 ^^^ vword c 2)
      (vword b 1 ^^^ vword a 3 ^^^ vword c 3) := by
  apply vec_ext
  intro e he
  simp only [sha1Su0, vword_xor]
  rw [vword_ofVWords _ _ _ _ he]
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;>
    congr 2 <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [vword, vdword, ofVDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append] <;>
    simp +arith (disch := omega) <;> simp_all +arith [show i ≤ 31 by omega, show i ≤ 63 by omega]

theorem su1_words (x y : BitVec 128) :
    sha1Su1 x y = ofVWords
      ((vword x 0 ^^^ vword y 1).rotateLeft 1)
      ((vword x 1 ^^^ vword y 2).rotateLeft 1)
      ((vword x 2 ^^^ vword y 3).rotateLeft 1)
      ((vword x 3).rotateLeft 1 ^^^ (vword x 0 ^^^ vword y 1).rotateLeft 2) := by
  simp (disch := omega) only [sha1Su1, vword_xor, vword_shr32,
    Nat.reduceLT, ite_true, ite_false, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.xor_zero]

theorem rotate_xor (a b : Word) (n : Nat) :
    (a ^^^ b).rotateLeft n = a.rotateLeft n ^^^ b.rotateLeft n := by
  ext i hi
  simp only [BitVec.getElem_rotateLeft, BitVec.getElem_xor]
  split_ifs <;> rfl

theorem rotate_twice (a : Word) : (a.rotateLeft 1).rotateLeft 1 = a.rotateLeft 2 := by
  ext i hi
  simp only [BitVec.getElem_rotateLeft]
  simp (disch := omega) only [Nat.reduceMod, Nat.reduceSub]
  split_ifs <;> first | omega | (congr 1 <;> omega)

theorem W_ge' (M : Block) (t : Nat) :
    W M (t + 16) = (W M (t + 13) ^^^ W M (t + 8) ^^^ W M (t + 2) ^^^ W M t).rotateLeft 1 := by
  rw [W_ge M (by omega), show t + 16 - 3 = t + 13 by omega, show t + 16 - 8 = t + 8 by omega,
    show t + 16 - 14 = t + 2 by omega, Nat.add_sub_cancel]

theorem schedule_eq (M : Block) (i : Nat) :
    sha1Su1 (sha1Su0 (quad M i) (quad M (i + 1)) (quad M (i + 2))) (quad M (i + 3)) =
      quad M (i + 4) := by
  simp only [su0_words, su1_words, quad, vword_ofVWords_0, vword_ofVWords_1,
    vword_ofVWords_2, vword_ofVWords_3]
  have w0 := W_ge' M (4 * i)
  have w1 := W_ge' M (4 * i + 1)
  have w2 := W_ge' M (4 * i + 2)
  have w3 := W_ge' M (4 * i + 3)
  simp only [show 4 * i + 16 = 4 * (i + 4) by omega, show 4 * i + 1 + 16 = 4 * (i + 4) + 1 by omega,
    show 4 * i + 2 + 16 = 4 * (i + 4) + 2 by omega, show 4 * i + 3 + 16 = 4 * (i + 4) + 3 by omega,
    show 4 * i + 13 = 4 * (i + 3) + 1 by omega, show 4 * i + 1 + 13 = 4 * (i + 3) + 2 by omega,
    show 4 * i + 2 + 13 = 4 * (i + 3) + 3 by omega,
    show 4 * i + 8 = 4 * (i + 2) by omega, show 4 * i + 1 + 8 = 4 * (i + 2) + 1 by omega,
    show 4 * i + 2 + 8 = 4 * (i + 2) + 2 by omega, show 4 * i + 3 + 8 = 4 * (i + 2) + 3 by omega,
    show 4 * i + 2 + 2 = 4 * (i + 1) by omega, show 4 * i + 3 + 2 = 4 * (i + 1) + 1 by omega,
    show 4 * i + 1 + 2 = 4 * i + 3 by omega] at w0 w1 w2 w3
  rw [w3, w0, w1, w2]
  simp only [rotate_xor, rotate_twice]
  ac_rfl

theorem eReg_words (v : HashValue) : eReg v = ofVWords v[4] 0 0 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [eReg, ofVWords, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    hi, decide_true, Bool.true_and, BitVec.ofNat_eq_ofNat]
  by_cases h : i < 32
  · simp only [h, ite_true]
  · simp only [h, ite_false, BitVec.getLsbD_zero, ite_self]
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem eReg_low (v : HashValue) : vword (eReg v) 0 = v[4] := by
  rw [eReg_words, vword_ofVWords_0]

theorem add_eReg (v H : HashValue) :
    VArr.s4.map2 (fun _ x y => x + y) (eReg v) (eReg H) = eReg (Vector.zipWith (· + ·) v H) := by
  simp only [eReg_words, VArr.map2, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2,
    vword_ofVWords_3, Vector.getElem_zipWith]
  rfl

end VG.Proof.Sha1.AArch64.Sha2
