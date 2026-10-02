import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Sha512.Spec

/-! The two-round SHA512H/H2 pair and the SHA512SU0/SU1 schedule. -/

namespace VG.Proof.Sha512.AArch64.Sha3

open VG.AArch64
open VG.Spec.Sha512 (HashValue Word Block K W ch maj bsig0 bsig1 ssig0 ssig1)

def ab (v : HashValue) : BitVec 128 := ofVDwords v[0] v[1]
def cd (v : HashValue) : BitVec 128 := ofVDwords v[2] v[3]
def ef (v : HashValue) : BitVec 128 := ofVDwords v[4] v[5]
def gh (v : HashValue) : BitVec 128 := ofVDwords v[6] v[7]
def pair (M : Block) (i : Nat) : BitVec 128 := ofVDwords (W M (2 * i)) (W M (2 * i + 1))
def t1 (v : HashValue) (k w : Word) : Word := v[7] + bsig1 v[4] + ch v[4] v[5] v[6] + k + w

theorem t1_eq (v : HashValue) (k w : Word) :
    ch v[4] v[5] v[6] + bsig1 v[4] + (k + w + v[7]) = t1 v k w := by
  unfold t1
  ac_rfl

theorem h_eq (v : HashValue) (k0 w0 k1 w1 : Word) :
    sha512H (ofVDwords (k1 + w1 + v[6]) (k0 + w0 + v[7]))
      (ofVDwords v[5] v[6]) (ofVDwords v[3] v[4]) =
    ofVDwords (t1 (roundKW v k0 w0) k1 w1) (t1 v k0 w0) := by
  simp only [sha512H, vdword_ofVDwords_0, vdword_ofVDwords_1]
  change ofVDwords
    (ch (ch v[4] v[5] v[6] + bsig1 v[4] + (k0 + w0 + v[7]) + v[3]) v[4] v[5] +
      bsig1 (ch v[4] v[5] v[6] + bsig1 v[4] + (k0 + w0 + v[7]) + v[3]) + (k1 + w1 + v[6]))
    (ch v[4] v[5] v[6] + bsig1 v[4] + (k0 + w0 + v[7])) = _
  rw [t1_eq]
  have he : t1 v k0 w0 + v[3] = (roundKW v k0 w0)[4] := by
    rw [roundKW_4]; unfold t1; ac_rfl
  rw [he]
  change ofVDwords
    (ch (roundKW v k0 w0)[4] (roundKW v k0 w0)[5] (roundKW v k0 w0)[6] +
      bsig1 (roundKW v k0 w0)[4] + (k1 + w1 + (roundKW v k0 w0)[7])) _ = _
  rw [t1_eq]

/-- SHA512H with `c` and `d` added to its accumulator and zero in place of `d`
in its third operand computes the next `e` and `f` themselves. -/
theorem hF_eq (v : HashValue) (k0 w0 k1 w1 : Word) :
    sha512H (ofVDwords (k1 + w1 + v[6] + v[2]) (k0 + w0 + v[7] + v[3]))
      (ofVDwords v[5] v[6]) (ofVDwords 0 v[4]) =
    ef (roundKW (roundKW v k0 w0) k1 w1) := by
  simp only [sha512H, vdword_ofVDwords_0, vdword_ofVDwords_1]
  rw [show ∀ x : Word, x + (0 : BitVec 64) = x from BitVec.add_zero]
  change ofVDwords
    (ch (ch v[4] v[5] v[6] + bsig1 v[4] + (k0 + w0 + v[7] + v[3])) v[4] v[5] +
      bsig1 (ch v[4] v[5] v[6] + bsig1 v[4] + (k0 + w0 + v[7] + v[3])) + (k1 + w1 + v[6] + v[2]))
    (ch v[4] v[5] v[6] + bsig1 v[4] + (k0 + w0 + v[7] + v[3])) = _
  have he : ch v[4] v[5] v[6] + bsig1 v[4] + (k0 + w0 + v[7] + v[3]) = (roundKW v k0 w0)[4] := by
    rw [roundKW_4]; ac_rfl
  rw [he]
  change ofVDwords
    (ch (roundKW v k0 w0)[4] (roundKW v k0 w0)[5] (roundKW v k0 w0)[6] +
      bsig1 (roundKW v k0 w0)[4] + (k1 + w1 + (roundKW v k0 w0)[7] + (roundKW v k0 w0)[3]))
    (roundKW v k0 w0)[4] = _
  have he' : ch (roundKW v k0 w0)[4] (roundKW v k0 w0)[5] (roundKW v k0 w0)[6] +
      bsig1 (roundKW v k0 w0)[4] + (k1 + w1 + (roundKW v k0 w0)[7] + (roundKW v k0 w0)[3]) =
      (roundKW (roundKW v k0 w0) k1 w1)[4] := by
    rw [roundKW_4 (v := roundKW v k0 w0)]; ac_rfl
  rw [he']
  rfl

theorem maj_rev (a b c : Word) : (c &&& b) ^^^ (c &&& a) ^^^ (b &&& a) = maj a b c := by
  ext i
  simp only [maj, BitVec.getElem_xor, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

theorem a_eq (v : HashValue) (k w : Word) :
    maj v[0] v[1] v[2] + bsig0 v[0] + t1 v k w = (roundKW v k w)[0] := by
  rw [roundKW_0]; unfold t1; ac_rfl

theorem h2_eq (v : HashValue) (k0 w0 k1 w1 : Word) :
    sha512H2 (ofVDwords (t1 (roundKW v k0 w0) k1 w1) (t1 v k0 w0)) (cd v) (ab v) =
      ab (roundKW (roundKW v k0 w0) k1 w1) := by
  simp only [sha512H2, ab, cd, vdword_ofVDwords_0, vdword_ofVDwords_1, maj_rev]
  change ofVDwords
    ((((maj v[0] v[1] v[2] + bsig0 v[0] + t1 v k0 w0) &&& v[0]) ^^^
      ((maj v[0] v[1] v[2] + bsig0 v[0] + t1 v k0 w0) &&& v[1]) ^^^ (v[1] &&& v[0])) +
      bsig0 (maj v[0] v[1] v[2] + bsig0 v[0] + t1 v k0 w0) + t1 (roundKW v k0 w0) k1 w1)
    (maj v[0] v[1] v[2] + bsig0 v[0] + t1 v k0 w0) = _
  rw [a_eq]
  have hc : v[1] &&& v[0] = v[0] &&& v[1] := BitVec.and_comm _ _
  rw [hc]
  change ofVDwords
    (maj (roundKW v k0 w0)[0] (roundKW v k0 w0)[1] (roundKW v k0 w0)[2] +
      bsig0 (roundKW v k0 w0)[0] + t1 (roundKW v k0 w0) k1 w1) _ = _
  rw [a_eq]
  rfl

theorem cd_eq (v : HashValue) (k0 w0 k1 w1 : Word) :
    cd (roundKW (roundKW v k0 w0) k1 w1) = ab v := rfl
theorem gh_eq (v : HashValue) (k0 w0 k1 w1 : Word) :
    gh (roundKW (roundKW v k0 w0) k1 w1) = ef v := rfl

theorem schedule_eq (M : Block) (i : Nat) :
    sha512Su1 (sha512Su0 (pair M i) (pair M (i + 1))) (pair M (i + 7))
      (ofVDwords (W M (2 * (i + 4) + 1)) (W M (2 * (i + 5)))) = pair M (i + 8) := by
  simp only [sha512Su0, sha512Su1, pair, vdword_ofVDwords_0, vdword_ofVDwords_1]
  have h0 := W_ge M (show 16 ≤ 2 * (i + 8) by omega)
  have h1 := W_ge M (show 16 ≤ 2 * (i + 8) + 1 by omega)
  rw [h0, h1]
  simp only [show 2 * (i + 8) - 2 = 2 * (i + 7) by omega,
    show 2 * (i + 8) - 7 = 2 * (i + 4) + 1 by omega,
    show 2 * (i + 8) - 15 = 2 * i + 1 by omega,
    show 2 * (i + 8) - 16 = 2 * i by omega,
    show 2 * (i + 8) + 1 - 2 = 2 * (i + 7) + 1 by omega,
    show 2 * (i + 8) + 1 - 7 = 2 * (i + 5) by omega,
    show 2 * (i + 8) + 1 - 15 = 2 * (i + 1) by omega,
    show 2 * (i + 8) + 1 - 16 = 2 * i + 1 by omega, ssig0, ssig1, add_ac]

theorem add_ab (v H : HashValue) :
    VArr.d2.map2 (fun _ x y => x + y) (ab v) (ab H) = ab (Vector.zipWith (· + ·) v H) := by
  simp only [VArr.map2, ab, vdword_ofVDwords_0, vdword_ofVDwords_1, Vector.getElem_zipWith]
theorem add_cd (v H : HashValue) :
    VArr.d2.map2 (fun _ x y => x + y) (cd v) (cd H) = cd (Vector.zipWith (· + ·) v H) := by
  simp only [VArr.map2, cd, vdword_ofVDwords_0, vdword_ofVDwords_1, Vector.getElem_zipWith]
theorem add_ef (v H : HashValue) :
    VArr.d2.map2 (fun _ x y => x + y) (ef v) (ef H) = ef (Vector.zipWith (· + ·) v H) := by
  simp only [VArr.map2, ef, vdword_ofVDwords_0, vdword_ofVDwords_1, Vector.getElem_zipWith]
theorem add_gh (v H : HashValue) :
    VArr.d2.map2 (fun _ x y => x + y) (gh v) (gh H) = gh (Vector.zipWith (· + ·) v H) := by
  simp only [VArr.map2, gh, vdword_ofVDwords_0, vdword_ofVDwords_1, Vector.getElem_zipWith]

end VG.Proof.Sha512.AArch64.Sha3
