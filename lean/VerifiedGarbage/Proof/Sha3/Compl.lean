import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Framework.Bitslice.Anf

/-!
# Keccak-f[1600]: a round on complemented lanes, as polynomials

Untrusted: everything here is checked by Lean.

Implementations that keep the lanes `complLanes` complemented (the "lane
complementing" transform) store `A[i] ⊕ msk i` for lane `i` of a state `A`
(`cmpl A`). A round of such an implementation is checked by evaluating its
code over the ANF domain (`Bitslice.Anf`), with the lanes of its input
state, as stored, as atoms `0–24` and the round constant as atom `25`, and
comparing what it stores with `specP`: the same round, computed over the
domain from the specification's `out` (`Proof/Sha3/Spec.lean`) on the
uncomplemented lanes, and complemented again. `eval_specP` says what that
is: lane `j` of the round's output, as stored.
-/

namespace VG.Proof.Sha3.Compl

open VG.Bitslice.Anf
open VG.Impl.Sha3 (rhoOff piSrc complLanes)
open VG.Spec.Sha3 (Lane)

/-- Lane `i` is kept complemented: all ones, or zero. -/
def msk (i : Nat) : Lane := if complLanes.contains i then BitVec.allOnes 64 else 0

/-- The state as stored: lanes `complLanes` complemented. -/
def cmpl (A : Spec.Sha3.State) : Spec.Sha3.State := Vector.ofFn fun i => A[i.val] ^^^ msk i.val

/-! ## The round over the ANF domain -/

def maskP (i : Nat) : Poly := if complLanes.contains i then one else zero

/-- Lane `i` of the state, from the lane as stored (atom `i`). -/
def sA (i : Nat) : Poly := pxor (atom i) (maskP i)

def sC (x : Nat) : Poly := pxor (pxor (pxor (pxor (sA x) (sA (x + 5))) (sA (x + 10))) (sA (x + 15))) (sA (x + 20))

def sD (x : Nat) : Poly := pxor (pror 63 (sC ((x + 1) % 5))) (sC ((x + 4) % 5))

def srotl (p : Poly) (k : Nat) : Poly := if k = 0 then p else pror (64 - k) p

def sB (x y : Nat) : Poly := srotl (pxor (sA (piSrc x y)) (sD ((x + 3 * y) % 5))) (rhoOff (piSrc x y))

def sOut (x y : Nat) : Poly :=
  let t := pxor (pand (pxor (sB ((x + 1) % 5) y) one) (sB ((x + 2) % 5) y)) (sB x y)
  if x = 0 ∧ y = 0 then pxor t (atom 25) else t

/-- Lane `j` of the round's output, as stored. -/
def specP (j : Nat) : Poly := pxor (sOut (j % 5) (j / 5)) (maskP j)

/-! ## What it is -/

section
variable {V : Nat → Lane} {A : Spec.Sha3.State}

theorem eval_maskP (i : Nat) : eval V (maskP i) = msk i := by
  unfold maskP msk; split
  · exact eval_one V
  · exact eval_zero V

theorem msk_msk (x : Lane) (i : Nat) : x ^^^ msk i ^^^ msk i = x := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem eval_sA (hV : ∀ i (hi : i < 25), V i = A[i] ^^^ msk i) {i : Nat} (hi : i < 25) :
    eval V (sA i) = A[i]! := by
  rw [sA, eval_pxor, eval_atom, eval_maskP, hV i hi, msk_msk, getElem!_eq _ hi]

theorem eval_sC (hV : ∀ i (hi : i < 25), V i = A[i] ^^^ msk i) {x : Nat} (hx : x < 5) :
    eval V (sC x) = C A x := by
  simp only [sC, eval_pxor, eval_sA hV (show x < 25 by omega), eval_sA hV (show x + 5 < 25 by omega),
    eval_sA hV (show x + 10 < 25 by omega), eval_sA hV (show x + 15 < 25 by omega),
    eval_sA hV (show x + 20 < 25 by omega), C]

theorem eval_sD (hV : ∀ i (hi : i < 25), V i = A[i] ^^^ msk i) (x : Nat) : eval V (sD x) = D A x := by
  simp only [sD, eval_pxor, eval_pror, eval_sC hV (Nat.mod_lt _ (by omega : 0 < 5)), D]

theorem eval_srotl (p : Poly) (k : Nat) : eval V (srotl p k) = rotl (eval V p) k := by
  unfold srotl rotl; split
  · rfl
  · exact eval_pror V _ _

theorem eval_sB (hV : ∀ i (hi : i < 25), V i = A[i] ^^^ msk i) {x y : Nat} (hx : x < 5) (_hy : y < 5) :
    eval V (sB x y) = B A x y := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega
  simp only [sB, eval_srotl, eval_pxor, eval_sA hV hj, eval_sD hV, B]

theorem eval_sOut (hV : ∀ i (hi : i < 25), V i = A[i] ^^^ msk i) {rc : Lane} (hrc : V 25 = rc)
    {x y : Nat} (hx : x < 5) (hy : y < 5) : eval V (sOut x y) = out A rc x y := by
  have h1 : (x + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h2 : (x + 2) % 5 < 5 := Nat.mod_lt _ (by omega)
  have e : ∀ v : Lane, eval V (pxor (pand (pxor (sB ((x + 1) % 5) y) one) (sB ((x + 2) % 5) y)) (sB x y)) =
      (B A ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B A ((x + 2) % 5) y ^^^ B A x y := fun _ => by
    rw [eval_pxor, eval_pand, eval_pxor, eval_one, eval_sB hV h1 hy, eval_sB hV h2 hy, eval_sB hV hx hy]
    rfl
  unfold sOut out
  simp only
  split
  · rw [eval_pxor, e 0, eval_atom, hrc]
  · exact e 0

theorem eval_specP (hV : ∀ i (hi : i < 25), V i = A[i] ^^^ msk i) {rc : Lane} (hrc : V 25 = rc)
    {j : Nat} (hj : j < 25) : eval V (specP j) = (cmpl (outState A rc))[j] := by
  simp only [specP, eval_pxor, eval_sOut hV hrc (Nat.mod_lt _ (by omega : 0 < 5)) (by omega : j / 5 < 5),
    eval_maskP, cmpl, outState, Vector.getElem_ofFn]

end

end VG.Proof.Sha3.Compl
