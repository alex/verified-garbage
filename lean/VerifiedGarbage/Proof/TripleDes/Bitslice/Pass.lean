import VerifiedGarbage.Proof.TripleDes.Bitslice.Round
import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.TripleDes.Word

/-!
# A bitsliced DES pass, lane by lane

Lane `b` of the state is the 64-bit value `ipLane W b`: the left half, then
the right half. A pass is eight pairs of rounds, the first reading the
right half and the second the left (`pairs`), so that no word moves, and
then the exchange of the halves (`swapW`): `pass_lane` proves that it does
in every lane what `desCore` (DES between IP and FP) does.
-/

namespace VG.Proof.TripleDes.Bitslice

open VG.Spec.TripleDes VG.Impl.TripleDes.Bitslice VG.Bitslice VG.Proof.TripleDes

variable {w : Nat}

/-- Lane `b`: the left half, then the right half. -/
def ipLane (W : Nat → BitVec w) (b : Nat) : BitVec 64 := half lWord W b ++ half rWord W b

/-- The first `n` pairs of rounds, with the key of round `r` (from 0) `key r`. -/
def pairs (key : Nat → BitVec 48) : Nat → (Nat → BitVec w) → Nat → BitVec w
  | 0, W => W
  | n + 1, W => roundW .ab (key (2 * n + 1)) (roundW .ba (key (2 * n)) (pairs key n W))

/-- The word of the other half's same bit, for the words of the halves. -/
def partner (x : Nat) : Option Nat :=
  match (List.range 32).find? (fun q => lWord q == x) with
  | some q => some (rWord q)
  | none => ((List.range 32).find? (fun q => rWord q == x)).map lWord

/-- Exchange the halves. -/
def swapW (W : Nat → BitVec w) : Nat → BitVec w := fun x =>
  match partner x with
  | some y => W y
  | none => W x

theorem partner_l : ∀ q < 32, partner (lWord q) = some (rWord q) := by decide +kernel
theorem partner_r : ∀ q < 32, partner (rWord q) = some (lWord q) := by decide +kernel

theorem swapW_half_l (W : Nat → BitVec w) (b : Nat) : half lWord (swapW W) b = half rWord W b := by
  apply BitVec.eq_of_getLsbD_eq
  intro q hq
  simp only [half, getLsbD_ofBits, hq, decide_true, Bool.true_and, swapW, partner_l q hq]

theorem swapW_half_r (W : Nat → BitVec w) (b : Nat) : half rWord (swapW W) b = half lWord W b := by
  apply BitVec.eq_of_getLsbD_eq
  intro q hq
  simp only [half, getLsbD_ofBits, hq, decide_true, Bool.true_and, swapW, partner_r q hq]

theorem readWord_ba : readWord .ba = rWord := rfl
theorem readWord_ab : readWord .ab = lWord := rfl
theorem writeWord_ba : writeWord .ba = lWord := rfl
theorem writeWord_ab : writeWord .ab = rWord := rfl

/-- `n` pairs of rounds are `2 n` Feistel steps, in every lane. -/
theorem pairs_halves (keys : DesSchedule) (d : Direction) (n : Nat) (W : Nat → BitVec w)
    {b : Nat} (hb : b < w) :
    (half lWord (pairs (roundKey keys d) n W) b, half rWord (pairs (roundKey keys d) n W) b) =
      roundPrefix keys d (2 * n) (half lWord W b, half rWord W b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [e, roundPrefix_succ, roundPrefix_succ, ← ih]
    simp only [pairs]
    obtain ⟨ba₁, ba₂⟩ := roundW_half .ba (roundKey keys d (2 * n)) (pairs (roundKey keys d) n W) hb
    obtain ⟨ab₁, ab₂⟩ := roundW_half .ab (roundKey keys d (2 * n + 1))
      (roundW .ba (roundKey keys d (2 * n)) (pairs (roundKey keys d) n W)) hb
    simp only [readWord_ba, readWord_ab, writeWord_ba, writeWord_ab] at ab₁ ab₂ ba₁ ba₂
    simp only [feistelStep]
    rw [ab₁, ab₂, ba₁, ba₂]

theorem ipLane_hi (W : Nat → BitVec w) (b : Nat) :
    ((ipLane W b >>> 32).setWidth 32) = half lWord W b := appended_left _ _

theorem ipLane_lo (W : Nat → BitVec w) (b : Nat) : (ipLane W b).setWidth 32 = half rWord W b :=
  appended_right _ _

/-- A pass: eight pairs of rounds, then the exchange of the halves. -/
def passW (keys : DesSchedule) (d : Direction) (W : Nat → BitVec w) : Nat → BitVec w :=
  swapW (pairs (roundKey keys d) 8 W)

theorem pass_lane (keys : DesSchedule) (d : Direction) (W : Nat → BitVec w) {b : Nat}
    (hb : b < w) : ipLane (passW keys d W) b = desCore keys d (ipLane W b) := by
  rw [desCore_roundPrefix]
  simp only [ipLane_hi, ipLane_lo]
  rw [← pairs_halves keys d 8 W hb]
  simp only [ipLane, passW, swapW_half_l, swapW_half_r]

end VG.Proof.TripleDes.Bitslice
