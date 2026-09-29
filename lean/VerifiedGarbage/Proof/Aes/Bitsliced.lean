import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.Framework.Bitslice.Table
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs

/-!
# Bitsliced AES: the layout and the round transformations

Untrusted: everything here is checked by Lean.

Four AES states in eight 64-bit words, as in BearSSL's `aes_ct64` (Thomas
Pornin, MIT licence): bit `j` of byte `i = r + 4c` of block `b` is bit
`pos b i = 16r + 4c + b` of word `j`. `BsRel Q S` says the words `Q`
hold the states `S`. The lemmas here turn what each layer of the code does
to the bits (as its proof states it) into the transformation of FIPS 197
it computes on the states. Nothing here depends on the target.
-/

namespace VG.Proof.Aes

open VG VG.Bitslice VG.Spec.Aes

/-- The byte at bit position `p` of eight words: its bit `k` is bit `p` of word `k`. -/
def bsByte (Q : Nat → BitVec 64) (p : Nat) : Byte := ofBits 8 fun k => (Q k).getLsbD p

theorem getLsbD_bsByte (Q : Nat → BitVec 64) (p : Nat) {k : Nat} (hk : k < 8) :
    (bsByte Q p).getLsbD k = (Q k).getLsbD p := by
  rw [bsByte, getLsbD_ofBits]; simp [hk]

/-- Byte `r + 4c` of block `b` is at position `16r + 4c + b`. -/
def pos (b i : Nat) : Nat := 16 * (i % 4) + 4 * (i / 4) + b

/-- The byte at position `p`. -/
def idx (p : Nat) : Nat := p / 16 + 4 * (p / 4 % 4)

theorem pos_lt {b i : Nat} (hb : b < 4) (hi : i < 16) : pos b i < 64 := by
  simp only [pos]; omega

/-- The words `Q` hold the four states `S`. -/
def BsRel (Q : Nat → BitVec 64) (S : Nat → State) : Prop :=
  ∀ b < 4, ∀ i < 16, bsByte Q (pos b i) = (S b).getD i 0

/-- The words `K` hold the round key `rk` in all four blocks. -/
def KeyRel (K : Nat → BitVec 64) (rk : List Byte) : Prop :=
  ∀ b < 4, ∀ i < 16, bsByte K (pos b i) = rk.getD i 0

/-- The words `Q` hold the four states byte by byte, little-endian:
bytes 0–7 of block `b` in word `b` and bytes 8–15 in word `b + 4`. -/
def InRel (Q : Nat → BitVec 64) (S : Nat → State) : Prop :=
  ∀ b < 4, ∀ i < 16, ∀ j < 8, (Q (b + 4 * (i / 8))).getLsbD (8 * (i % 8) + j) = ((S b).getD i 0).getLsbD j

theorem getD_eq {α : Type} {n : Nat} (xs : Vector α n) {i : Nat} (h : i < n) (d : α) :
    xs.getD i d = xs[i] := by
  simp [Vector.getD, Array.getD, h]

theorem byte_ext {x y : Byte} (h : ∀ j < 8, x.getLsbD j = y.getLsbD j) : x = y :=
  BitVec.eq_of_getLsbD_eq fun j hj => h j hj

/-! ## The layers -/

theorem bs_subBytes {Q Q' : Nat → BitVec 64} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 64, (Q' j).getLsbD p = (sbox (bsByte Q p)).getLsbD j) (hr : BsRel Q S) :
    BsRel Q' fun b => subBytes (S b) := by
  intro b hb i hi
  have : bsByte Q' (pos b i) = sbox (bsByte Q (pos b i)) :=
    byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi)]
  rw [this, hr b hb i hi, getD_eq _ hi, getD_eq _ hi]
  simp only [subBytes, Vector.getElem_map]

/-- ShiftRows: position `16r + 4c + b` from `16r + 4((c + r) mod 4) + b`. -/
def srSrc (p : Nat) : Nat := 16 * (p / 16) + 4 * ((p / 4 % 4 + p / 16) % 4) + p % 4

theorem srSrc_pos : ∀ b < 4, ∀ i < 16, srSrc (pos b i) = pos b (i % 4 + 4 * ((i / 4 + i % 4) % 4)) := by
  decide

theorem bs_shiftRows {Q Q' : Nat → BitVec 64} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 64, (Q' j).getLsbD p = (Q j).getLsbD (srSrc p)) (hr : BsRel Q S) :
    BsRel Q' fun b => shiftRows (S b) := by
  intro b hb i hi
  have : bsByte Q' (pos b i) = bsByte Q (pos b (i % 4 + 4 * ((i / 4 + i % 4) % 4))) :=
    byte_ext fun j hj => by
      rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi), srSrc_pos b hb i hi]
  rw [this, hr b hb _ (by omega), getD_eq _ hi]
  simp only [shiftRows, Vector.getElem_ofFn]

theorem bs_addRoundKey {Q Q' K : Nat → BitVec 64} {S : Nat → State} {rk : List Byte}
    (h : ∀ j < 8, ∀ p < 64, (Q' j).getLsbD p = ((Q j).getLsbD p ^^ (K j).getLsbD p))
    (hr : BsRel Q S) (hk : KeyRel K rk) : BsRel Q' fun b => addRoundKey (S b) rk := by
  intro b hb i hi
  have : bsByte Q' (pos b i) = bsByte Q (pos b i) ^^^ bsByte K (pos b i) :=
    byte_ext fun j hj => by
      rw [BitVec.getLsbD_xor, getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj,
        h j hj _ (pos_lt hb hi)]
  rw [this, hr b hb i hi, hk b hb i hi, getD_eq _ hi, getD_eq _ hi]
  simp only [addRoundKey, Vector.getElem_ofFn, getD_eq _ hi]

theorem idx_pos : ∀ b < 4, ∀ i < 16, pos b i % 4 = b ∧ idx (pos b i) = i := by decide

theorem bs_of_in {Q Q' : Nat → BitVec 64} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 64, (Q' j).getLsbD p =
      (Q (p % 4 + 4 * (idx p / 8))).getLsbD (8 * (idx p % 8) + j)) (hr : InRel Q S) :
    BsRel Q' S := by
  intro b hb i hi
  refine byte_ext fun j hj => ?_
  obtain ⟨h1, h2⟩ := idx_pos b hb i hi
  rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi), h1, h2, hr b hb i hi j hj]

theorem in_of_bs {Q Q' : Nat → BitVec 64} {S : Nat → State}
    (h : ∀ k < 8, ∀ t < 64, (Q' k).getLsbD t = (Q (t % 8)).getLsbD (pos (k % 4) (t / 8 + 8 * (k / 4))))
    (hr : BsRel Q S) : InRel Q' S := by
  intro b hb i hi j hj
  rw [h _ (by omega) _ (by omega), ← getLsbD_bsByte _ _ (by omega)]
  rw [show (8 * (i % 8) + j) % 8 = j by omega, show (b + 4 * (i / 8)) % 4 = b by omega,
    show (8 * (i % 8) + j) / 8 + 8 * ((b + 4 * (i / 8)) / 4) = i by omega, hr b hb i hi]

/-! ## MixColumns -/

theorem mul2 (a : Byte) : mul 0x02 a = xtimes a := by
  simp [mul, List.range, List.range.loop, Nat.repeat]

theorem mul3 (a : Byte) : mul 0x03 a = xtimes a ^^^ a := by
  simp [mul, List.range, List.range.loop, Nat.repeat, BitVec.xor_comm]

theorem xtimes_bit (a : Byte) {j : Nat} (hj : j < 8) : (xtimes a).getLsbD j =
    ((if j = 0 then false else a.getLsbD (j - 1)) ^^
      (decide (j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4) && a.getLsbD 7)) := by
  simp only [xtimes, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.msb_eq_getLsbD_last]
  cases h : a.getLsbD 7 <;> (interval_cases j <;> simp_all)

/-- The XOR of the bits `(w, t)` (bit `t` of word `w`). -/
def termsXor (Q : Nat → BitVec 64) (l : List (Nat × Nat)) : Bool :=
  l.foldr (fun wt b => (Q wt.1).getLsbD wt.2 ^^ b) false

/-- Position `p` moved `k` rows down (within its column). -/
def down (p k : Nat) : Nat := (p + 16 * k) % 64

/-- Bit `j` of MixColumns at position `p`, as BearSSL computes it: with
`u = a₀ ⊕ a₁` (the byte and the next one in its column), `{02} • u`
moves bit `j - 1` of `u` to `j` and adds bit 7 at the bits of `{1b}`;
then add `a₁ ⊕ a₂ ⊕ a₃`. -/
def mcWords (j : Nat) : List (Nat × Nat) :=
  (if j = 0 then [] else [(j - 1, 0), (j - 1, 1)]) ++
  (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then [(7, 0), (7, 1)] else []) ++ [(j, 1), (j, 2), (j, 3)]

/-- The bits `(w, k)` of `mcWords`: bit `w` of the byte `k` rows down. -/
def mcTerms (j p : Nat) : List (Nat × Nat) := (mcWords j).map fun wk => (wk.1, down p wk.2)

theorem down_pos : ∀ b < 4, ∀ i < 16, ∀ k < 4,
    down (pos b i) k = pos b ((i % 4 + k) % 4 + 4 * (i / 4)) := by
  decide

theorem termsXor_mc (Q : Nat → BitVec 64) (j p : Nat) : termsXor Q (mcTerms j p) =
    ((if j = 0 then false else ((Q (j - 1)).getLsbD (down p 0) ^^ (Q (j - 1)).getLsbD (down p 1))) ^^
     (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then (Q 7).getLsbD (down p 0) ^^ (Q 7).getLsbD (down p 1)
      else false) ^^
     ((Q j).getLsbD (down p 1) ^^ (Q j).getLsbD (down p 2) ^^ (Q j).getLsbD (down p 3))) := by
  simp only [mcTerms, mcWords]
  split_ifs <;> simp [termsXor]

theorem bs_mixColumns {Q Q' : Nat → BitVec 64} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 64, (Q' j).getLsbD p = termsXor Q (mcTerms j p)) (hr : BsRel Q S) :
    BsRel Q' fun b => mixColumns (S b) := by
  intro b hb i hi
  refine byte_ext fun j hj => ?_
  have hbit : ∀ k < 4, ∀ w < 8, (Q w).getLsbD (down (pos b i) k) =
      ((S b).getD ((i % 4 + k) % 4 + 4 * (i / 4)) 0).getLsbD w := fun k hk w hw => by
    rw [down_pos b hb i hi k hk, ← hr b hb _ (by omega), getLsbD_bsByte _ _ hw]
  rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi), getD_eq _ hi, termsXor_mc]
  simp only [mixColumns, Vector.getElem_ofFn, mul2, mul3, BitVec.getLsbD_xor, xtimes_bit _ hj]
  simp only [hbit 1 (by decide) _ hj, hbit 2 (by decide) _ hj,
    hbit 3 (by decide) _ hj, hbit 0 (by decide) 7 (by decide), hbit 1 (by decide) 7 (by decide),
    hbit 0 (by decide) (j - 1) (by omega), hbit 1 (by decide) (j - 1) (by omega)]
  generalize ((S b).getD ((i % 4 + 0) % 4 + 4 * (i / 4)) 0) = a0
  generalize ((S b).getD ((i % 4 + 1) % 4 + 4 * (i / 4)) 0) = a1
  generalize ((S b).getD ((i % 4 + 2) % 4 + 4 * (i / 4)) 0) = a2
  generalize ((S b).getD ((i % 4 + 3) % 4 + 4 * (i / 4)) 0) = a3
  by_cases h1 : (j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4) <;>
    simp only [h1, ite_true, ite_false, decide_true, decide_false, Bool.true_and,
      Bool.false_and, Bool.xor_false] <;>
    by_cases h0 : j = 0 <;>
    simp only [h0, ite_true, ite_false, Bool.false_xor, Bool.xor_assoc,
      Bool.xor_comm, Bool.xor_left_comm]

end VG.Proof.Aes
