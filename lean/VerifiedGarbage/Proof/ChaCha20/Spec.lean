import VerifiedGarbage.Spec.ChaCha20

/-!
# Facts about the ChaCha20 specification

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20

open VG.Spec.ChaCha20 (Word quarterRound qround)

abbrev CState := Spec.ChaCha20.State

theorem rotateLeft_eq (x : Word) {k : Nat} (hk : 0 < k) (hk' : k < 32) :
    x.rotateLeft k = x.rotateRight (32 - k) := by
  ext i hi
  simp only [BitVec.getElem_rotateLeft, BitVec.getElem_rotateRight]
  split <;> split <;> first | (exfalso; omega) | exact getElem_congr rfl (by omega) _

/-- `quarterRound` with the rotations the code does. -/
theorem quarterRound_eq (a b c d : Word) : quarterRound a b c d =
    let a := a + b; let d := (d ^^^ a).rotateRight 16
    let c := c + d; let b := (b ^^^ c).rotateRight 20
    let a := a + b; let d := (d ^^^ a).rotateRight 24
    let c := c + d; let b := (b ^^^ c).rotateRight 25
    (a, b, c, d) := by
  simp only [quarterRound, rotateLeft_eq _ (show 0 < 16 by decide) (by decide),
    rotateLeft_eq _ (show 0 < 12 by decide) (by decide), rotateLeft_eq _ (show 0 < 8 by decide) (by decide),
    rotateLeft_eq _ (show 0 < 7 by decide) (by decide)]

theorem qround_get (v : CState) (x y z w : Fin 16) (k : Nat) (hk : k < 16) :
    (qround v x y z w)[k]'hk =
      if w.1 = k then (quarterRound (v[x]'x.isLt) (v[y]'y.isLt) (v[z]'z.isLt) (v[w]'w.isLt)).2.2.2
      else if z.1 = k then (quarterRound (v[x]'x.isLt) (v[y]'y.isLt) (v[z]'z.isLt) (v[w]'w.isLt)).2.2.1
      else if y.1 = k then (quarterRound (v[x]'x.isLt) (v[y]'y.isLt) (v[z]'z.isLt) (v[w]'w.isLt)).2.1
      else if x.1 = k then (quarterRound (v[x]'x.isLt) (v[y]'y.isLt) (v[z]'z.isLt) (v[w]'w.isLt)).1
      else v[k]'hk := by
  simp only [qround, Vector.getElem_set]

end VG.Proof.ChaCha20
