import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Pass
import VerifiedGarbage.Proof.TripleDes.Schedule

/-!
# The keys of the three passes

Pass `p` (counted down from 3) reads the round keys at `passA d p S + r δ`:
these are the round keys, in DES's order for the pass's direction, of the
component of the schedule `S` that TDEA uses in that pass (`passComp`).
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.Impl.TripleDes.X86_64.Bitslice VG.Spec.TripleDes
open VG.Proof.TripleDes (roundKey componentSchedule_readW)

/-- The component of the schedule and the direction of pass `p`. -/
def passComp : Direction → Nat → Nat × Direction
  | .encrypt, 3 => (0, .encrypt)
  | .encrypt, 2 => (1, .decrypt)
  | .encrypt, _ => (2, .encrypt)
  | .decrypt, 3 => (2, .decrypt)
  | .decrypt, 2 => (1, .encrypt)
  | .decrypt, _ => (0, .decrypt)

/-- The schedule word that is round `r`'s key of pass `p`. -/
def passIdx (d : Direction) (p r : Nat) : Nat :=
  16 * (passComp d p).1 + if (passComp d p).2 = .encrypt then r else 15 - r

theorem passIdx_lt : ∀ d : Direction, ∀ p, 1 ≤ p → p ≤ 3 → ∀ r < 16, passIdx d p r < 48 := by
  intro d p h1 h3 r hr
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> first | omega | (simp [passIdx, passComp]; omega)

theorem passAddr_eq : ∀ d : Direction, ∀ p, 1 ≤ p → p ≤ 3 → ∀ r < 16,
    BitVec.ofNat 64 (passKey d p).1 + BitVec.ofNat 64 r * BitVec.ofInt 64 (passKey d p).2 =
      BitVec.ofNat 64 (8 * passIdx d p r) := by
  intro d p h1 h3
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> first | omega | decide

theorem keyAt_pass (m : Mem) (S : Addr) (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {r : Nat}
    (hr : r < 16) :
    keyAt m (passA d p S) (passD d p) r =
      roundKey (componentSchedule (scheduleAt m S) (passComp d p).1) (passComp d p).2 r := by
  simp only [keyAt, passA, passD, roundKey]
  have hc : (passComp d p).1 < 3 := by
    cases d <;> (rcases hp with ⟨h1, h3⟩; rcases p with _ | _ | _ | _ | p) <;> first | omega | decide
  have hi : (if (passComp d p).2 = .encrypt then r else 15 - r) < 16 := by split <;> omega
  rw [componentSchedule_readW m S _ _ hc hi, BitVec.add_assoc, passAddr_eq d p hp.1 hp.2 r hr]
  rfl

/-- The key words of the passes are apart from the scratch buffer. -/
theorem passKeys_apart {s : State} {S : Addr} (hS : ∀ i < 48, Apart s (S + BitVec.ofNat 64 (8 * i)))
    (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {r : Nat} (hr : r < 16) :
    Apart s (passA d p S + BitVec.ofNat 64 r * passD d p) := by
  simp only [passA, passD]
  rw [BitVec.add_assoc, passAddr_eq d p hp.1 hp.2 r hr]
  exact hS _ (passIdx_lt d p hp.1 hp.2 r hr)

end VG.Proof.TripleDes.X86_64.Bitsliced
