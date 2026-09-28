import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.Bitslice.Table

/-!
# Words of atoms, for checking linear layers

Untrusted: everything here is checked by Lean.

The lane domain (`Bitslice.lanes`) evaluates straight-line code that only
moves and XORs bits of 64-bit words, and masks them with constants, on
input words given as atoms: bit `t` of input word `i` is atom `64 i + t`.
An output word whose bit `p` is the XOR of the atoms `g p` is related to the
machine's word when bit `p` of it is the XOR of the input bits `g p`
(`outWord_rel`). Each ISA's `Framework/<ISA>/Linear.lean` runs its
evaluator with these.
-/

namespace VG.Bitslice

/-- Input word `i`: bit `t` is atom `64 i + t`. -/
def inWord (i : Nat) : Nat × Nat := (0, mk 64 (fun t => [64 * i + t]) 64)

/-- The word whose bit `p` is the XOR of the atoms `g p`. -/
def outWord (g : Nat → List Nat) : Nat × Nat := (0, mk 64 g 64)

/-- Bit `a % 64` of word `a / 64`. -/
def bitOf (W : Nat → BitVec 64) (a : Nat) : Bool := (W (a / 64)).getLsbD (a % 64)

/-- The XOR of the bits `l` of the words `W`. -/
def xorBits (W : Nat → BitVec 64) (l : List Nat) : Bool := l.foldr (fun a b => bitOf W a ^^ b) false

@[simp] theorem xorBits_nil (W : Nat → BitVec 64) : xorBits W [] = false := rfl

@[simp] theorem xorBits_cons (W : Nat → BitVec 64) (a : Nat) (l : List Nat) :
    xorBits W (a :: l) = (bitOf W a ^^ xorBits W l) := rfl

theorem bitOf_word (W : Nat → BitVec 64) (i t : Nat) (ht : t < 64) :
    bitOf W (64 * i + t) = (W i).getLsbD t := by
  simp only [bitOf]
  rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt ht, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt ht]

/-- The assignment of the atoms below `N` given by the words `W`. -/
def assign (W : Nat → BitVec 64) (N : Nat) : Nat := tableOf (bitOf W) N

theorem xorA_assign (W : Nat → BitVec 64) {N : Nat} {l : List Nat} (hl : ∀ a ∈ l, a < N) :
    xorA (assign W N) l = xorBits W l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [xorA, List.foldr_cons, xorBits_cons] at ih ⊢
    rw [ih fun b hb => hl b (by simp [hb]), assign, testBit_tableOf]
    simp [hl a (by simp)]

theorem inWord_rel {k : Nat} (W : Nat → BitVec 64) {i : Nat} (hi : 64 * i + 64 ≤ 2 ^ k) :
    LaneRel k (assign W (2 ^ k)) (inWord i) (W i) := by
  refine ⟨Nat.two_pow_pos _, fun q hq => ?_⟩
  simp only [inWord, Nat.zero_testBit, Bool.false_xor]
  rw [par_mk hq (Nat.le_refl _) _ (fun q' hq' a ha => by simp at ha; omega), xorA_assign W
    (by intro a ha; simp at ha; omega)]
  simp [hq, bitOf_word W i q hq]

theorem outWord_rel {k : Nat} {W : Nat → BitVec 64} {g : Nat → List Nat} {x : BitVec 64}
    (hg : ∀ p < 64, ∀ a ∈ g p, a < 2 ^ k) (h : LaneRel k (assign W (2 ^ k)) (outWord g) x) :
    ∀ p < 64, x.getLsbD p = xorBits W (g p) := by
  intro p hp
  rw [h.2 p hp]
  simp only [outWord, Nat.zero_testBit, Bool.false_xor]
  rw [par_mk hp (Nat.le_refl _) _ (fun q hq => hg q hq), xorA_assign W (hg p hp)]
  simp [hp]

end VG.Bitslice
