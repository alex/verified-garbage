import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Sha256.Spec

/-!
# SHA-256 with the SHA extensions: the values in the SSE registers

Untrusted: everything here is checked by Lean. How the working variables,
the message schedule and the constants are laid out in SSE registers, and
that `sha256rnds2` and `sha256msg1`/`sha256msg2` compute rounds and schedule
words of `Spec/Sha256.lean`.
-/

namespace VG.Proof.Sha256.X86_64.ShaNi

open VG VG.X86_64
open VG.Spec.Sha256 (HashValue Word Block K W ch maj bsig0 bsig1 ssig0 ssig1)

/-- The working variables `A, B, E, F`, as `sha256rnds2` takes and returns them
(`A` in bits 127:96). -/
def abef (v : HashValue) : BitVec 128 := ofDwords v[5] v[4] v[1] v[0]

/-- The working variables `C, D, G, H` (`C` in bits 127:96). -/
def cdgh (v : HashValue) : BitVec 128 := ofDwords v[7] v[6] v[3] v[2]

/-- After two rounds, `C, D, G, H` are the old `A, B, E, F`. -/
theorem cdgh_two (v : HashValue) (k0 w0 k1 w1 : Word) :
    cdgh (roundKW (roundKW v k0 w0) k1 w1) = abef v := rfl

/-- `sha256rnds2` does two rounds, given `Wₜ + Kₜ` for them in the low doublewords of `x`. -/
theorem rnds2_eq (v : HashValue) (x : BitVec 128) {k0 w0 k1 w1 : Word}
    (h0 : dword x 0 = k0 + w0) (h1 : dword x 1 = k1 + w1) :
    sha256Rnds2 (cdgh v) (abef v) x = abef (roundKW (roundKW v k0 w0) k1 w1) := by
  have ech : sha256Ch = ch := rfl
  have emaj : sha256Maj = maj := rfl
  have es0 : sha256BigSigma0 = bsig0 := rfl
  have es1 : sha256BigSigma1 = bsig1 := rfl
  simp only [sha256Rnds2, abef, cdgh, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, h0, h1, ech, emaj, es0, es1, roundKW_0, roundKW_1, roundKW_2, roundKW_3,
    roundKW_4, roundKW_5, roundKW_6, roundKW_7]
  generalize v[0]'(by decide) = a
  generalize v[1]'(by decide) = b
  generalize v[2]'(by decide) = c
  generalize v[3]'(by decide) = d
  generalize v[4]'(by decide) = e
  generalize v[5]'(by decide) = f
  generalize v[6]'(by decide) = g
  generalize v[7]'(by decide) = h
  have e1 : ch e f g + bsig1 e + (k0 + w0) + h + d = d + (h + bsig1 e + ch e f g + k0 + w0) := by ac_rfl
  have a1 : ch e f g + bsig1 e + (k0 + w0) + h + maj a b c + bsig0 a =
      h + bsig1 e + ch e f g + k0 + w0 + (bsig0 a + maj a b c) := by ac_rfl
  rw [e1, a1]
  generalize d + (h + bsig1 e + ch e f g + k0 + w0) = e₁
  generalize h + bsig1 e + ch e f g + k0 + w0 + (bsig0 a + maj a b c) = a₁
  have e2 : ch e₁ e f + bsig1 e₁ + (k1 + w1) + g + c = c + (g + bsig1 e₁ + ch e₁ e f + k1 + w1) := by ac_rfl
  have a2 : ch e₁ e f + bsig1 e₁ + (k1 + w1) + g + maj a₁ a b + bsig0 a₁ =
      g + bsig1 e₁ + ch e₁ e f + k1 + w1 + (bsig0 a₁ + maj a₁ a b) := by ac_rfl
  rw [e2, a2]

/-- The message schedule words `W₄ᵢ … W₄ᵢ₊₃` (`W₄ᵢ` in bits 31:0). -/
def quad (M : Block) (i : Nat) : BitVec 128 :=
  ofDwords (W M (4 * i)) (W M (4 * i + 1)) (W M (4 * i + 2)) (W M (4 * i + 3))

theorem W_ge' (M : Block) (t : Nat) :
    W M (t + 16) = ssig1 (W M (t + 14)) + W M (t + 9) + ssig0 (W M (t + 1)) + W M t := by
  rw [W_ge M (by omega)]; rfl

/-- `W_ge'`, summed in the order of `sha256msg1` and `sha256msg2`. -/
theorem W_ge_rev (M : Block) (t : Nat) :
    W M (t + 16) = W M t + ssig0 (W M (t + 1)) + W M (t + 9) + ssig1 (W M (t + 14)) := by
  rw [W_ge' M t]; ac_rfl

/-- `sha256msg1`, `palignr` and `sha256msg2` compute the next four schedule words
from the previous sixteen. -/
theorem schedule_eq (M : Block) (i : Nat) :
    sha256Msg2 (XBinOp.eval .paddd (XBinOp.eval .sha256msg1 (quad M i) (quad M (i + 1)))
        (alignRight (quad M (i + 3)) (quad M (i + 2)) 4)) (quad M (i + 3)) = quad M (i + 4) := by
  have ess0 : sha256Sigma0 = ssig0 := rfl
  have ess1 : sha256Sigma1 = ssig1 := rfl
  simp only [sha256Msg2, XBinOp.eval, alignRight_4, quad, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3, ess0, ess1]
  have w0 := W_ge_rev M (4 * i)
  have w1 := W_ge_rev M (4 * i + 1)
  have w2 := W_ge_rev M (4 * i + 2)
  have w3 := W_ge_rev M (4 * i + 3)
  simp only [show 4 * i + 16 = 4 * (i + 4) by omega, show 4 * i + 1 + 16 = 4 * (i + 4) + 1 by omega,
    show 4 * i + 2 + 16 = 4 * (i + 4) + 2 by omega, show 4 * i + 3 + 16 = 4 * (i + 4) + 3 by omega,
    show 4 * i + 14 = 4 * (i + 3) + 2 by omega, show 4 * i + 1 + 14 = 4 * (i + 3) + 3 by omega,
    show 4 * i + 9 = 4 * (i + 2) + 1 by omega, show 4 * i + 1 + 9 = 4 * (i + 2) + 2 by omega,
    show 4 * i + 2 + 9 = 4 * (i + 2) + 3 by omega, show 4 * i + 3 + 9 = 4 * (i + 3) by omega,
    show 4 * i + 1 + 1 = 4 * i + 2 by omega, show 4 * i + 2 + 1 = 4 * i + 3 by omega,
    show 4 * i + 3 + 1 = 4 * (i + 1) by omega] at w0 w1 w2 w3 ⊢
  rw [w2, w3, w0, w1]

/-- Adding the working variables into the hash value, two registers at a time. -/
theorem paddd_abef (v H : HashValue) :
    XBinOp.eval .paddd (abef v) (abef H) = abef (Vector.zipWith (· + ·) v H) := by
  simp only [XBinOp.eval, abef, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, Vector.getElem_zipWith]

theorem paddd_cdgh (v H : HashValue) :
    XBinOp.eval .paddd (cdgh v) (cdgh H) = cdgh (Vector.zipWith (· + ·) v H) := by
  simp only [XBinOp.eval, cdgh, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, Vector.getElem_zipWith]

end VG.Proof.Sha256.X86_64.ShaNi
