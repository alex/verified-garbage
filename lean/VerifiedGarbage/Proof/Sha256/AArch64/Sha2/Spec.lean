import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Sha256.Spec

/-! SHA-256 rounds and scheduling as computed by the AArch64 SHA instructions. -/

namespace VG.Proof.Sha256.AArch64.Sha2

open VG.AArch64
open VG.Spec.Sha256 (HashValue Word Block K W ch maj bsig0 bsig1 ssig0 ssig1)

def abcd (v : HashValue) : BitVec 128 := ofVWords v[0] v[1] v[2] v[3]
def efgh (v : HashValue) : BitVec 128 := ofVWords v[4] v[5] v[6] v[7]

theorem choose_eq (x y z : Word) : shaChoose x y z = ch x y z := (ch_eq x y z).symm

theorem majority_eq (x y z : Word) : shaMajority x y z = maj x y z := by
  rw [maj_eq, BitVec.or_comm]; rfl

theorem step_eq (v : HashValue) (k w : Word) :
    sha256Step (k + w) (abcd v, efgh v) = (abcd (roundKW v k w), efgh (roundKW v k w)) := by
  simp only [sha256Step, abcd, efgh, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2, vword_ofVWords_3,
    choose_eq, majority_eq,
    show shaHashSigma0 = bsig0 from rfl, show shaHashSigma1 = bsig1 from rfl,
    roundKW_0, roundKW_1, roundKW_2, roundKW_3, roundKW_4, roundKW_5, roundKW_6, roundKW_7]
  congr 2 <;> ac_rfl

/-- Four hardware rounds, using the old ABCD for the second instruction. -/
theorem hash_eq (v : HashValue) (q : BitVec 128) (k0 w0 k1 w1 k2 w2 k3 w3 : Word)
    (h0 : vword q 0 = k0 + w0) (h1 : vword q 1 = k1 + w1)
    (h2 : vword q 2 = k2 + w2) (h3 : vword q 3 = k3 + w3) (part : Bool) :
    sha256Hash (abcd v) (efgh v) q part =
      if part then abcd (roundKW (roundKW (roundKW (roundKW v k0 w0) k1 w1) k2 w2) k3 w3)
      else efgh (roundKW (roundKW (roundKW (roundKW v k0 w0) k1 w1) k2 w2) k3 w3) := by
  simp only [sha256Hash, h0, h1, h2, h3, step_eq]

def quad (M : Block) (i : Nat) : BitVec 128 :=
  ofVWords (W M (4 * i)) (W M (4 * i + 1)) (W M (4 * i + 2)) (W M (4 * i + 3))

theorem W_ge' (M : Block) (t : Nat) :
    W M (t + 16) = ssig1 (W M (t + 14)) + (ssig0 (W M (t + 1)) + W M t) + W M (t + 9) := by
  rw [W_ge M (by omega)]
  simp only [show t + 16 - 2 = t + 14 by omega, show t + 16 - 7 = t + 9 by omega,
    show t + 16 - 15 = t + 1 by omega, show t + 16 - 16 = t by omega]
  ac_rfl

theorem schedule_eq (M : Block) (i : Nat) :
    sha256Su1 (sha256Su0 (quad M i) (quad M (i + 1))) (quad M (i + 2)) (quad M (i + 3)) =
      quad M (i + 4) := by
  simp only [sha256Su1, sha256Su0, quad, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2, vword_ofVWords_3]
  change ofVWords
    (ssig1 (W M (4 * (i + 3) + 2)) + (ssig0 (W M (4 * i + 1)) + W M (4 * i)) + W M (4 * (i + 2) + 1))
    (ssig1 (W M (4 * (i + 3) + 3)) + (ssig0 (W M (4 * i + 2)) + W M (4 * i + 1)) + W M (4 * (i + 2) + 2))
    (ssig1 _ + (ssig0 (W M (4 * i + 3)) + W M (4 * i + 2)) + W M (4 * (i + 2) + 3))
    (ssig1 _ + (ssig0 (W M (4 * (i + 1))) + W M (4 * i + 3)) + W M (4 * (i + 3))) = _
  have w0 := W_ge' M (4 * i)
  have w1 := W_ge' M (4 * i + 1)
  have w2 := W_ge' M (4 * i + 2)
  have w3 := W_ge' M (4 * i + 3)
  simp only [show 4 * i + 16 = 4 * (i + 4) by omega, show 4 * i + 1 + 16 = 4 * (i + 4) + 1 by omega,
    show 4 * i + 2 + 16 = 4 * (i + 4) + 2 by omega, show 4 * i + 3 + 16 = 4 * (i + 4) + 3 by omega,
    show 4 * i + 14 = 4 * (i + 3) + 2 by omega, show 4 * i + 1 + 14 = 4 * (i + 3) + 3 by omega,
    show 4 * i + 9 = 4 * (i + 2) + 1 by omega, show 4 * i + 1 + 9 = 4 * (i + 2) + 2 by omega,
    show 4 * i + 2 + 9 = 4 * (i + 2) + 3 by omega, show 4 * i + 3 + 9 = 4 * (i + 3) by omega,
    show 4 * i + 1 + 1 = 4 * i + 2 by omega, show 4 * i + 2 + 1 = 4 * i + 3 by omega,
    show 4 * i + 3 + 1 = 4 * (i + 1) by omega] at w0 w1 w2 w3
  rw [w2, w3, w0, w1]
  rfl

theorem add_abcd (v H : HashValue) :
    VArr.s4.map2 (fun _ x y => x + y) (abcd v) (abcd H) = abcd (Vector.zipWith (· + ·) v H) := by
  simp only [VArr.map2, abcd, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2,
    vword_ofVWords_3, Vector.getElem_zipWith]

theorem add_efgh (v H : HashValue) :
    VArr.s4.map2 (fun _ x y => x + y) (efgh v) (efgh H) = efgh (Vector.zipWith (· + ·) v H) := by
  simp only [VArr.map2, efgh, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2,
    vword_ofVWords_3, Vector.getElem_zipWith]

end VG.Proof.Sha256.AArch64.Sha2
