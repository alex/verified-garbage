import VerifiedGarbage.Proof.TripleDes.Bitslice.Layout
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.Framework.Bitslice.Table

/-!
# A bitsliced DES round, lane by lane

The state is 64 words of `w` bits (`W : Nat → BitVec w`); lane `b` of the
halves is bit `b` of their words (`half`). A round reads one half and XORs
`f` into the other (`Role`): for each S-box `j`, in order, `step` XORs its
four outputs, computed at every bit position from the words of `E` and the
round key's bits, into their words. `roundW_half` proves that a round does
in every lane what DES's round does to the halves.
-/

namespace VG.Proof.TripleDes.Bitslice

open VG.Spec.TripleDes VG.Impl.TripleDes.Bitslice VG.Bitslice VG.Proof.TripleDes

variable {w : Nat}

/-- Lane `b` of the half whose bit `q` is in the word `word q`. -/
def half (word : Nat → Nat) (W : Nat → BitVec w) (b : Nat) : BitVec 32 :=
  ofBits 32 fun q => (W (word q)).getLsbD b

/-- S-box `j`'s input in lane `b`: the words of `E` and the key's bits. -/
def sboxIn (ρ : Role) (k : BitVec 48) (j : Nat) (W : Nat → BitVec w) (b : Nat) : BitVec 6 :=
  ofBits 6 fun i => (W (readWord ρ (eBit (inBit j i)))).getLsbD b ^^ k.getLsbD (inBit j i)

/-- S-box `j`'s output bit `i`, in every lane. -/
def sboxOut (ρ : Role) (k : BitVec 48) (j : Nat) (W : Nat → BitVec w) (i : Nat) : BitVec w :=
  ofBits w fun b => (sBox j (sboxIn ρ k j W b)).getLsbD i

/-- The output bit of S-box `j` that goes into the word `x`, if any. -/
def outIdx (ρ : Role) (j x : Nat) : Option Nat :=
  (List.range 4).find? fun i => writeWord ρ (outBit j i) == x

/-- S-box `j`'s step: XOR its outputs into their words. -/
def step (ρ : Role) (k : BitVec 48) (j : Nat) (W : Nat → BitVec w) : Nat → BitVec w := fun x =>
  match outIdx ρ j x with
  | some i => W x ^^^ sboxOut ρ k j W i
  | none => W x

/-- The first `n` S-boxes' steps. -/
def steps (ρ : Role) (k : BitVec 48) (n : Nat) (W : Nat → BitVec w) : Nat → BitVec w :=
  (List.range n).foldl (fun W j => step ρ k j W) W

/-- A round. -/
def roundW (ρ : Role) (k : BitVec 48) (W : Nat → BitVec w) : Nat → BitVec w := steps ρ k 8 W

theorem steps_succ (ρ : Role) (k : BitVec 48) (n : Nat) (W : Nat → BitVec w) :
    steps ρ k (n + 1) W = step ρ k n (steps ρ k n W) := by
  simp only [steps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## Which words a step writes -/

/-- The S-box output that is bit `q` of `f`: S-box `src q / 4`, bit `src q % 4`. -/
def src (q : Nat) : Nat := ((List.range 32).find? fun x => outBit (x / 4) (x % 4) == q).getD 0

theorem src_spec : ∀ q < 32, src q < 32 ∧ outBit (src q / 4) (src q % 4) = q := by decide +kernel

theorem outIdx_read : ∀ ρ : Role, ∀ j < 8, ∀ q < 32, outIdx ρ j (readWord ρ q) = none := by
  intro ρ; cases ρ <;> decide +kernel

theorem outIdx_write : ∀ ρ : Role, ∀ j < 8, ∀ q < 32,
    outIdx ρ j (writeWord ρ q) = if j = src q / 4 then some (src q % 4) else none := by
  intro ρ; cases ρ <;> decide +kernel

theorem step_read (ρ : Role) (k : BitVec 48) {j q : Nat} (hj : j < 8) (hq : q < 32)
    (W : Nat → BitVec w) : step ρ k j W (readWord ρ q) = W (readWord ρ q) := by
  simp only [step, outIdx_read ρ j hj q hq]

theorem steps_read (ρ : Role) (k : BitVec 48) {n q : Nat} (hn : n ≤ 8) (hq : q < 32)
    (W : Nat → BitVec w) : steps ρ k n W (readWord ρ q) = W (readWord ρ q) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [steps_succ, step_read ρ k (by omega) hq, ih (by omega)]

theorem sboxIn_steps (ρ : Role) (k : BitVec 48) {n j : Nat} (hn : n ≤ 8) (hj : j < 8)
    (W : Nat → BitVec w) (b : Nat) : sboxIn ρ k j (steps ρ k n W) b = sboxIn ρ k j W b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [sboxIn, getLsbD_ofBits, hi, decide_true, Bool.true_and,
    steps_read ρ k hn (eBit_lt j hj i hi)]

/-- After the first `n` steps, bit `b` of the word of bit `q` of the written half. -/
theorem steps_write (ρ : Role) (k : BitVec 48) {n q : Nat} (hn : n ≤ 8) (hq : q < 32)
    (W : Nat → BitVec w) (b : Nat) :
    (steps ρ k n W (writeWord ρ q)).getLsbD b = ((W (writeWord ρ q)).getLsbD b ^^
      (decide (src q / 4 < n) &&
        (decide (b < w) && (sBox (src q / 4) (sboxIn ρ k (src q / 4) W b)).getLsbD (src q % 4)))) := by
  induction n with
  | zero => simp [steps]
  | succ n ih =>
    rw [steps_succ]
    simp only [step, outIdx_write ρ n (by omega) q hq]
    have hs := (src_spec q hq).1
    by_cases he : n = src q / 4
    · subst he
      simp only [ite_true, BitVec.getLsbD_xor, ih (by omega), sboxOut, getLsbD_ofBits,
        sboxIn_steps ρ k (n := src q / 4) (j := src q / 4) (by omega) (by omega)]
      have h1 : ¬ src q / 4 < src q / 4 := by omega
      have h2 : src q / 4 < src q / 4 + 1 := by omega
      simp [h1, h2]
    · simp only [he, ite_false, ih (by omega)]
      have : (src q / 4 < n + 1) ↔ (src q / 4 < n) := by omega
      simp only [decide_eq_decide.mpr this]

/-! ## The round function, lane by lane -/

theorem sboxIn_eq (ρ : Role) (k : BitVec 48) {j : Nat} (hj : j < 8) (W : Nat → BitVec w)
    (b : Nat) : sboxIn ρ k j W b =
      ((permute expansion (half (readWord ρ) W b) ^^^ k) >>> (6 * (7 - j))).setWidth 6 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have he := eBit_lt j hj i hi
  have hin := inBit_lt j hj i hi
  simp only [sboxIn, getLsbD_ofBits, hi, decide_true, Bool.true_and, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  have hidx' : 6 * (7 - j) + i = inBit j i := rfl
  simp only [hidx']
  rw [permute_bit expansion _ (by decide) _ hin]
  simp only [half, getLsbD_ofBits, eBit] at he ⊢
  simp [he]

/-- Bit `q` of `f`, in lane `b`, is the output of the S-box it comes from. -/
theorem roundFunction_lane (ρ : Role) (k : BitVec 48) (W : Nat → BitVec w) (b : Nat) {q : Nat}
    (hq : q < 32) : (roundFunction (half (readWord ρ) W b) k).getLsbD q =
      (sBox (src q / 4) (sboxIn ρ k (src q / 4) W b)).getLsbD (src q % 4) := by
  obtain ⟨hs, ho⟩ := src_spec q hq
  have hj : src q / 4 < 8 := by omega
  have hi : src q % 4 < 4 := Nat.mod_lt _ (by decide)
  have spec := outBit_spec _ hj _ hi
  rw [ho] at spec
  rw [roundFunction_bit _ _ q hq, sboxIn_eq ρ k hj]
  simp only [spec]
  have e1 : 7 - (4 * (7 - src q / 4) + src q % 4) / 4 = src q / 4 := by omega
  have e2 : (4 * (7 - src q / 4) + src q % 4) % 4 = src q % 4 := by omega
  rw [e1, e2]

/-- A round XORs DES's `f` of the half it reads into the half it writes,
and leaves the half it reads, in every lane. -/
theorem roundW_half (ρ : Role) (k : BitVec 48) (W : Nat → BitVec w) {b : Nat} (hb : b < w) :
    half (writeWord ρ) (roundW ρ k W) b =
        half (writeWord ρ) W b ^^^ roundFunction (half (readWord ρ) W b) k ∧
      half (readWord ρ) (roundW ρ k W) b = half (readWord ρ) W b := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    have hj : src q / 4 < 8 := by have := (src_spec q hq).1; omega
    have l1 : (half (writeWord ρ) (roundW ρ k W) b).getLsbD q =
        (roundW ρ k W (writeWord ρ q)).getLsbD b := by
      simp only [half, getLsbD_ofBits, hq, decide_true, Bool.true_and]
    have l2 : (half (writeWord ρ) W b).getLsbD q = (W (writeWord ρ q)).getLsbD b := by
      simp only [half, getLsbD_ofBits, hq, decide_true, Bool.true_and]
    rw [BitVec.getLsbD_xor, l1, l2, roundFunction_lane ρ k W b hq, roundW,
      steps_write ρ k (by decide) hq]
    simp [hj, hb]
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    simp only [half, getLsbD_ofBits, hq, decide_true, Bool.true_and, roundW,
      steps_read ρ k (n := 8) (by decide) hq]

theorem sboxIn_congr (ρ : Role) (k : BitVec 48) {j : Nat} (hj : j < 8) {W W' : Nat → BitVec w}
    (hW : ∀ x < 64, W x = W' x) (b : Nat) : sboxIn ρ k j W b = sboxIn ρ k j W' b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hr : readWord ρ (eBit (inBit j i)) < 64 := by
    have := eBit_lt j hj i hi
    cases ρ
    · exact rWord_lt _ this
    · exact lWord_lt _ this
  simp only [sboxIn, getLsbD_ofBits, hi, decide_true, Bool.true_and, hW _ hr]

theorem step_congr (ρ : Role) (k : BitVec 48) {j : Nat} (hj : j < 8) {W W' : Nat → BitVec w}
    (hW : ∀ y < 64, W y = W' y) {x : Nat} (hx : W x = W' x) : step ρ k j W x = step ρ k j W' x := by
  simp only [step]
  split
  · rename_i i _
    rw [hx]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    simp only [sboxOut, getLsbD_ofBits, hb, decide_true, Bool.true_and, sboxIn_congr ρ k hj hW b]
  · exact hx

theorem outIdx_lt64 : ∀ ρ : Role, ∀ j < 8, ∀ x, outIdx ρ j x ≠ none → x < 64 := by
  intro ρ j hj x hx
  have key : ∀ ρ : Role, ∀ j < 8, ∀ i < 4, writeWord ρ (outBit j i) < 64 := by
    intro ρ; cases ρ <;> decide +kernel
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hx
  have hm := List.find?_some hi
  have hl := List.mem_range.mp (List.mem_of_find?_eq_some hi)
  simp only [beq_iff_eq] at hm
  rw [← hm]; exact key ρ j hj i hl

/-- The steps read and write only the 64 state words. -/
theorem steps_congr (ρ : Role) (k : BitVec 48) {n : Nat} (hn : n ≤ 8) {W W' : Nat → BitVec w}
    (hW : ∀ x < 64, W x = W' x) : ∀ x < 64, steps ρ k n W x = steps ρ k n W' x := by
  induction n with
  | zero => exact hW
  | succ n ih =>
    intro x hx
    have ih' := ih (by omega)
    rw [steps_succ, steps_succ]
    simp only [step]
    split
    · rename_i i _
      rw [ih' x hx]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro b hb
      simp only [sboxOut, getLsbD_ofBits, hb, decide_true, Bool.true_and,
        sboxIn_congr ρ k (by omega : n < 8) ih' b]
    · exact ih' x hx

theorem steps_high (ρ : Role) (k : BitVec 48) {n : Nat} (hn : n ≤ 8) (W : Nat → BitVec w)
    {x : Nat} (hx : 64 ≤ x) : steps ρ k n W x = W x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [steps_succ]
    have : outIdx ρ n x = none := by
      cases h : outIdx ρ n x with
      | none => rfl
      | some i =>
        have := outIdx_lt64 ρ n (by omega) x (by rw [h]; exact Option.some_ne_none i)
        omega
    simp only [step, this, ih (by omega)]

/-- The words of neither half are left alone. -/
theorem roundW_other (ρ : Role) (k : BitVec 48) (W : Nat → BitVec w) {x : Nat}
    (hx : ∀ q < 32, x ≠ writeWord ρ q) : roundW ρ k W x = W x := by
  have key : ∀ n ≤ 8, steps ρ k n W x = W x := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [steps_succ]
      have : outIdx ρ n x = none := by
        unfold outIdx
        rw [List.find?_eq_none]
        intro i hi
        simp only [List.mem_range] at hi
        have := hx (outBit n i) (outBit_lt n (by omega) i hi)
        simp [Ne.symm this]
      simp only [step, this, ih (by omega)]
  exact key 8 (Nat.le_refl _)

end VG.Proof.TripleDes.Bitslice
