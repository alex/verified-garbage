import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Proof.Framework.Arm.Linear
import Mathlib.Tactic.SplitIfs

/-!
# Bitsliced AES in 32-bit words: the layout and the round transformations

Untrusted: everything here is checked by Lean.

As `Proof/Aes/Bitsliced.lean`, for two AES states in eight 32-bit words,
as in BearSSL's `aes_ct` (Thomas Pornin, MIT licence): bit `j` of byte
`i = r + 4c` of block `b` is bit `pos b i = 8r + 2c + b` of word `j`.
`BsRel Q S` says the words `Q` hold the states `S`. The lemmas here turn
what each layer of the code does to the bits (as its proof states it) into
the transformation of FIPS 197 it computes on the states; the byte-level
facts about `xtimes` are shared with the 64-bit layout.

The last section gives each linear layer as atoms (as the last section of
`Proof/Aes/Bitsliced.lean` does), for the checks by evaluation
(`Framework/Arm/Linear.lean`): bit `t`
of input word `i` is atom `32 i + t`.
-/

namespace VG.Proof.Aes.Arm

open VG VG.Bitslice VG.Spec.Aes
open VG.Proof.Aes (byte_ext getD_eq mul2 mul3 xtimes_bit)

/-- The byte at bit position `p` of eight words: its bit `k` is bit `p` of word `k`. -/
def bsByte (Q : Nat → BitVec 32) (p : Nat) : Byte := ofBits 8 fun k => (Q k).getLsbD p

theorem getLsbD_bsByte (Q : Nat → BitVec 32) (p : Nat) {k : Nat} (hk : k < 8) :
    (bsByte Q p).getLsbD k = (Q k).getLsbD p := by
  rw [bsByte, getLsbD_ofBits]; simp [hk]

/-- Byte `r + 4c` of block `b` is at position `8r + 2c + b`. -/
def pos (b i : Nat) : Nat := 8 * (i % 4) + 2 * (i / 4) + b

theorem pos_lt {b i : Nat} (hb : b < 2) (hi : i < 16) : pos b i < 32 := by
  simp only [pos]; omega

/-- The words `Q` hold the two states `S`. -/
def BsRel (Q : Nat → BitVec 32) (S : Nat → State) : Prop :=
  ∀ b < 2, ∀ i < 16, bsByte Q (pos b i) = (S b).getD i 0

/-- The words `K` hold the round key `rk` in both blocks. -/
def KeyRel (K : Nat → BitVec 32) (rk : List Byte) : Prop :=
  ∀ b < 2, ∀ i < 16, bsByte K (pos b i) = rk.getD i 0

/-- The words `Q` hold the two states word by word, little-endian: bytes
`4k … 4k + 3` of block `b` in word `2k + b`. -/
def InRel (Q : Nat → BitVec 32) (S : Nat → State) : Prop :=
  ∀ b < 2, ∀ i < 16, ∀ j < 8,
    (Q (2 * (i / 4) + b)).getLsbD (8 * (i % 4) + j) = ((S b).getD i 0).getLsbD j

/-! ## The layers -/

theorem bs_subBytes {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = (sbox (bsByte Q p)).getLsbD j) (hr : BsRel Q S) :
    BsRel Q' fun b => subBytes (S b) := by
  intro b hb i hi
  have : bsByte Q' (pos b i) = sbox (bsByte Q (pos b i)) :=
    byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi)]
  rw [this, hr b hb i hi, getD_eq _ hi, getD_eq _ hi]
  simp only [subBytes, Vector.getElem_map]

/-- ShiftRows: position `8r + 2c + b` from `8r + 2((c + r) mod 4) + b`. -/
def srSrc (p : Nat) : Nat := 8 * (p / 8) + 2 * ((p % 8 / 2 + p / 8) % 4) + p % 2

theorem srSrc_pos : ∀ b < 2, ∀ i < 16, srSrc (pos b i) = pos b (i % 4 + 4 * ((i / 4 + i % 4) % 4)) := by
  decide

theorem bs_shiftRows {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = (Q j).getLsbD (srSrc p)) (hr : BsRel Q S) :
    BsRel Q' fun b => shiftRows (S b) := by
  intro b hb i hi
  have : bsByte Q' (pos b i) = bsByte Q (pos b (i % 4 + 4 * ((i / 4 + i % 4) % 4))) :=
    byte_ext fun j hj => by
      rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi), srSrc_pos b hb i hi]
  rw [this, hr b hb _ (by omega), getD_eq _ hi]
  simp only [shiftRows, Vector.getElem_ofFn]

theorem bs_addRoundKey {Q Q' K : Nat → BitVec 32} {S : Nat → State} {rk : List Byte}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = ((Q j).getLsbD p ^^ (K j).getLsbD p))
    (hr : BsRel Q S) (hk : KeyRel K rk) : BsRel Q' fun b => addRoundKey (S b) rk := by
  intro b hb i hi
  have : bsByte Q' (pos b i) = bsByte Q (pos b i) ^^^ bsByte K (pos b i) :=
    byte_ext fun j hj => by
      rw [BitVec.getLsbD_xor, getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj,
        h j hj _ (pos_lt hb hi)]
  rw [this, hr b hb i hi, hk b hb i hi, getD_eq _ hi, getD_eq _ hi]
  simp only [addRoundKey, Vector.getElem_ofFn, getD_eq _ hi]

theorem pos_div : ∀ b < 2, ∀ i < 16, pos b i % 8 = 2 * (i / 4) + b ∧ pos b i / 8 = i % 4 := by
  decide

/-- `ortho` from the words of the blocks to the bitsliced state. -/
theorem bs_of_in {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = (Q (p % 8)).getLsbD (8 * (p / 8) + j))
    (hr : InRel Q S) : BsRel Q' S := by
  intro b hb i hi
  refine byte_ext fun j hj => ?_
  obtain ⟨h1, h2⟩ := pos_div b hb i hi
  rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi), h1, h2, hr b hb i hi j hj]

/-- `ortho` from the bitsliced state back to the words of the blocks. -/
theorem in_of_bs {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ k < 8, ∀ t < 32, (Q' k).getLsbD t = (Q (t % 8)).getLsbD (8 * (t / 8) + k))
    (hr : BsRel Q S) : InRel Q' S := by
  intro b hb i hi j hj
  rw [h _ (by omega) _ (by omega), ← getLsbD_bsByte _ _ (by omega)]
  rw [show (8 * (i % 4) + j) % 8 = j by omega,
    show 8 * ((8 * (i % 4) + j) / 8) + (2 * (i / 4) + b) = pos b i by simp only [pos]; omega,
    hr b hb i hi]

/-! ## MixColumns -/

/-- The XOR of the bits `(w, t)` (bit `t` of word `w`). -/
def termsXor (Q : Nat → BitVec 32) (l : List (Nat × Nat)) : Bool :=
  l.foldr (fun wt b => (Q wt.1).getLsbD wt.2 ^^ b) false

/-- Position `p` moved `k` rows down (within its column). -/
def down (p k : Nat) : Nat := (p + 8 * k) % 32

/-- The bits `(w, k)` of `Proof.Aes.mcWords`: bit `w` of the byte `k` rows down. -/
def mcTerms (j p : Nat) : List (Nat × Nat) := (Proof.Aes.mcWords j).map fun wk => (wk.1, down p wk.2)

theorem down_pos : ∀ b < 2, ∀ i < 16, ∀ k < 4,
    down (pos b i) k = pos b ((i % 4 + k) % 4 + 4 * (i / 4)) := by
  decide

theorem termsXor_mc (Q : Nat → BitVec 32) (j p : Nat) : termsXor Q (mcTerms j p) =
    ((if j = 0 then false else ((Q (j - 1)).getLsbD (down p 0) ^^ (Q (j - 1)).getLsbD (down p 1))) ^^
     (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then (Q 7).getLsbD (down p 0) ^^ (Q 7).getLsbD (down p 1)
      else false) ^^
     ((Q j).getLsbD (down p 1) ^^ (Q j).getLsbD (down p 2) ^^ (Q j).getLsbD (down p 3))) := by
  simp only [mcTerms, Proof.Aes.mcWords]
  split_ifs <;> simp [termsXor]

theorem bs_mixColumns {Q Q' : Nat → BitVec 32} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = termsXor Q (mcTerms j p)) (hr : BsRel Q S) :
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

/-! ## The linear layers, as atoms -/

/-- `ortho` (both ways): bit `j` at position `p` from bit `8 ⌊p / 8⌋ + j` of
word `p mod 8`. -/
def orthoG (j p : Nat) : List Nat := [32 * (p % 8) + (8 * (p / 8) + j)]

def srG (j p : Nat) : List Nat := [32 * j + srSrc p]

/-- MixColumns: the bits `mcTerms`, as atoms. -/
def mcG (j p : Nat) : List Nat := (mcTerms j p).map fun wt => 32 * wt.1 + wt.2

/-- AddRoundKey: the round key is input words `8 … 15`. -/
def arkG (j p : Nat) : List Nat := [32 * j + p, 32 * (8 + j) + p]

open VG.Arm.Straight in
theorem xorBits_map (W : Nat → BitVec 32) (l : List (Nat × Nat)) (hl : ∀ wt ∈ l, wt.2 < 32) :
    Arm.Straight.xorBits W (l.map fun wt => 32 * wt.1 + wt.2) = termsXor W l := by
  induction l with
  | nil => rfl
  | cons wt l ih =>
    simp only [List.map_cons, Arm.Straight.xorBits_cons, termsXor, List.foldr_cons] at ih ⊢
    rw [Arm.Straight.bitOf_word _ _ _ (hl wt (by simp)), ih fun v hv => hl v (by simp [hv])]

end VG.Proof.Aes.Arm
