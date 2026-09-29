import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Sha1.Spec

/-!
# SHA-1 with the SHA extensions: the values in the SSE registers

Untrusted: everything here is checked by Lean. How the working variables,
the message schedule and the constants are laid out in SSE registers, and
that `sha1rnds4`, `sha1nexte` and `sha1msg1`/`sha1msg2` compute rounds and
schedule words of `Spec/Sha1.lean`.
-/

namespace VG.Proof.Sha1.X86_64.ShaNi

open VG VG.X86_64
open VG.Spec.Sha1 (HashValue Word Block K W f)

/-- The working variables `A, B, C, D`, as `sha1rnds4` takes and returns them
(`A` in bits 127:96). -/
def abcd (v : HashValue) : BitVec 128 := ofDwords v[3] v[2] v[1] v[0]

/-- The working variable `E` in bits 127:96, and zeros. -/
def eReg (v : HashValue) : BitVec 128 := ofDwords 0 0 0 v[4]

/-- The message schedule words `W₄ᵢ … W₄ᵢ₊₃` (`W₄ᵢ` in bits 127:96). -/
def quad (M : Block) (i : Nat) : BitVec 128 :=
  ofDwords (W M (4 * i + 3)) (W M (4 * i + 2)) (W M (4 * i + 1)) (W M (4 * i))

/-! ## Rounds -/

/-- One round in group `g` of 20 rounds, as `sha1rnds4` computes it. -/
def hw (g : Nat) (v : HashValue) (w : Word) : HashValue :=
  #v[sha1F g v[1] v[2] v[3] + v[0].rotateLeft 5 + w + v[4] + sha1K g, v[0], v[1].rotateLeft 30, v[2],
    v[3]]

theorem f_eq {t : Nat} (ht : t < 80) : f t = sha1F (t / 20) := by
  funext x y z
  simp only [f, Spec.Sha1.ch, Spec.Sha1.parity, Spec.Sha1.maj]
  rcases (by omega : t < 20 ∨ (20 ≤ t ∧ t < 40) ∨ (40 ≤ t ∧ t < 60) ∨ 60 ≤ t) with h | h | h | h
  · simp only [h, ite_true, Nat.div_eq_of_lt h]; rfl
  · simp only [show ¬ t < 20 by omega, h.2, ite_false, ite_true, show t / 20 = 1 by omega]; rfl
  · simp only [show ¬ t < 20 by omega, show ¬ t < 40 by omega, h.2, ite_false, ite_true,
      show t / 20 = 2 by omega]; rfl
  · simp only [show ¬ t < 20 by omega, show ¬ t < 40 by omega, show ¬ t < 60 by omega, ite_false,
      show t / 20 = 3 by omega]; rfl

theorem K_eq {t : Nat} (ht : t < 80) : K t = sha1K (t / 20) := by
  simp only [K]
  rcases (by omega : t < 20 ∨ (20 ≤ t ∧ t < 40) ∨ (40 ≤ t ∧ t < 60) ∨ 60 ≤ t) with h | h | h | h
  · simp only [h, ite_true, Nat.div_eq_of_lt h]; rfl
  · simp only [show ¬ t < 20 by omega, h.2, ite_false, ite_true, show t / 20 = 1 by omega]; rfl
  · simp only [show ¬ t < 20 by omega, show ¬ t < 40 by omega, h.2, ite_false, ite_true,
      show t / 20 = 2 by omega]; rfl
  · simp only [show ¬ t < 20 by omega, show ¬ t < 40 by omega, show ¬ t < 60 by omega, ite_false,
      show t / 20 = 3 by omega]; rfl

/-- A round of the specification is `hw` of its group. -/
theorem round_hw (M : Block) (v : HashValue) {t : Nat} (ht : t < 80) :
    Spec.Sha1.round M v t = hw (t / 20) v (W M t) := by
  rw [round_eq, f_eq ht, K_eq ht]
  simp only [roundKW, hw]
  refine congrArg (fun x => #v[x, v[0], v[1].rotateLeft 30, v[2], v[3]]) ?_
  ac_rfl

/-- Four rounds in group `g`. -/
def hw4 (g : Nat) (v : HashValue) (w0 w1 w2 w3 : Word) : HashValue :=
  hw g (hw g (hw g (hw g v w0) w1) w2) w3

theorem hw4_e (g : Nat) (v : HashValue) (w0 w1 w2 w3 : Word) :
    (hw4 g v w0 w1 w2 w3)[4] = v[0].rotateLeft 30 := rfl

theorem imm_eq {g : Nat} (hg : g < 4) : ((BitVec.ofNat 8 g).extractLsb' 0 2).toNat = g := by
  rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- `sha1rnds4` does four rounds of group `g`, given `W₀ + E` in bits 127:96 of
its source and `W₁ … W₃` below. -/
theorem rnds4_eq (v : HashValue) {g : Nat} (hg : g < 4) (w0 w1 w2 w3 : Word) :
    sha1Rnds4 (abcd v) (ofDwords w3 w2 w1 (w0 + v[4])) (BitVec.ofNat 8 g) =
      abcd (hw4 g v w0 w1 w2 w3) := by
  simp only [sha1Rnds4, imm_eq hg, abcd, hw4, hw, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ← BitVec.add_assoc]

/-! ## The value added to the first message word -/

theorem zero_add32 (x : Word) : (0 : Word) + x = x := by simp

/-- In the first four rounds, `E` is added by `paddd`. -/
theorem paddd_e (v : HashValue) (M : Block) :
    XBinOp.eval .paddd (eReg v) (quad M 0) =
      ofDwords (W M (4 * 0 + 3)) (W M (4 * 0 + 2)) (W M (4 * 0 + 1)) (W M (4 * 0) + v[4]) := by
  simp only [XBinOp.eval, eReg, quad, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, BitVec.add_comm v[4], zero_add32]

/-- After that, `E` is `A` of four rounds before, rotated left by 30, which
`sha1nexte` adds. -/
theorem nexte_e (x : BitVec 128) (M : Block) (i : Nat) :
    XBinOp.eval .sha1nexte x (quad M i) =
      ofDwords (W M (4 * i + 3)) (W M (4 * i + 2)) (W M (4 * i + 1))
        (W M (4 * i) + (dword x 3).rotateLeft 30) := by
  simp only [XBinOp.eval, quad, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

/-! ## The message schedule -/

theorem dword_xor (x y : BitVec 128) (k : Nat) : dword (x ^^^ y) k = dword x k ^^^ dword y k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_dword, BitVec.getLsbD_xor, decide_eq_true hi, Bool.true_and]

theorem W_ge' (M : Block) (t : Nat) :
    W M (t + 16) = (W M (t + 13) ^^^ W M (t + 8) ^^^ W M (t + 2) ^^^ W M t).rotateLeft 1 := by
  rw [W_ge M (by omega), show t + 16 - 3 = t + 13 by omega, show t + 16 - 8 = t + 8 by omega,
    show t + 16 - 14 = t + 2 by omega, Nat.add_sub_cancel]

/-- `sha1msg1`, `pxor` and `sha1msg2` compute the next four schedule words
from the previous sixteen. -/
theorem schedule_eq (M : Block) (i : Nat) :
    sha1Msg2 (XBinOp.eval .pxor (XBinOp.eval .sha1msg1 (quad M i) (quad M (i + 1))) (quad M (i + 2)))
      (quad M (i + 3)) = quad M (i + 4) := by
  simp only [sha1Msg2, XBinOp.eval, quad, dword_xor, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3]
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
    show 4 * i + 1 + 2 = 4 * i + 3 by omega] at w0 w1 w2 w3 ⊢
  rw [w3, w0, w1, w2]
  ac_rfl

/-! ## Adding the working variables into the hash value -/

theorem paddd_abcd (v H : HashValue) :
    XBinOp.eval .paddd (abcd v) (abcd H) = abcd (Vector.zipWith (· + ·) v H) := by
  simp only [XBinOp.eval, abcd, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, Vector.getElem_zipWith]

theorem nexte_eReg (x : BitVec 128) (v H : HashValue) (hx : (dword x 3).rotateLeft 30 = v[4]) :
    XBinOp.eval .sha1nexte x (eReg H) = eReg (Vector.zipWith (· + ·) v H) := by
  simp only [XBinOp.eval, eReg, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, Vector.getElem_zipWith, hx, BitVec.add_comm H[4]]

end VG.Proof.Sha1.X86_64.ShaNi
