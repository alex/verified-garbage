import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Sha512.Spec
import VerifiedGarbage.Spec.Sha256

/-!
# 64-bit words as pairs of 32-bit halves

Untrusted: everything here is checked by Lean. The halves (`lo`, `hi`) of
sums, bitwise operations, rotations and shifts of 64-bit words, in the form
32-bit code computes them, the halves of a 64-bit word in memory, and of the
message length the padding ends with; for any 32-bit target (ARMv7, x86),
whose implementations define `lo` and `hi` as here.
-/

namespace VG.Proof.Sha512.Word64

/-- The low half of a 64-bit word. -/
def lo (x : BitVec 64) : BitVec 32 := x.extractLsb' 0 32

/-- The high half of a 64-bit word. -/
def hi (x : BitVec 64) : BitVec 32 := x.extractLsb' 32 32

/-! ## Halves -/

theorem lo_toNat (x : BitVec 64) : (lo x).toNat = x.toNat % 2 ^ 32 := by
  simp [lo]

theorem hi_toNat (x : BitVec 64) : (hi x).toNat = x.toNat / 2 ^ 32 := by
  simp only [hi, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

@[simp] theorem lo_zero : lo 0#64 = 0#32 := rfl

@[simp] theorem hi_zero : hi 0#64 = 0#32 := rfl

theorem eq_of_lo_hi {x y : BitVec 64} (h1 : lo x = lo y) (h2 : hi x = hi y) : x = y := by
  have e1 := congrArg BitVec.toNat h1
  have e2 := congrArg BitVec.toNat h2
  rw [lo_toNat, lo_toNat] at e1
  rw [hi_toNat, hi_toNat] at e2
  apply BitVec.eq_of_toNat_eq
  omega

theorem hi_append_lo (x : BitVec 64) : hi x ++ lo x = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (lo x).isLt, Nat.shiftLeft_eq, lo_toNat,
    hi_toNat]
  omega

theorem lo_append (a b : BitVec 32) : lo (a ++ b) = b := by
  simp only [lo]; exact BitVec.extractLsb'_append_eq_right

theorem hi_append (a b : BitVec 32) : hi (a ++ b) = a := by
  simp only [hi]; exact BitVec.extractLsb'_append_eq_left

/-- The carry out of the addition of the low halves (as `adds` sets it). -/
theorem lo_add (x y : BitVec 64) : lo (x + y) = lo x + lo y := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo_toNat, BitVec.toNat_add]
  omega

theorem hi_add (x y : BitVec 64) :
    hi (x + y) = hi x + hi y + (if 2 ^ 32 ≤ (lo x).toNat + (lo y).toNat then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [hi_toNat, lo_toNat, BitVec.toNat_add]
  have := x.isLt; have := y.isLt
  split <;> simp <;> omega

theorem lo_xor (x y : BitVec 64) : lo (x ^^^ y) = lo x ^^^ lo y := by
  simp [lo, BitVec.extractLsb'_xor]

theorem hi_xor (x y : BitVec 64) : hi (x ^^^ y) = hi x ^^^ hi y := by
  simp [hi, BitVec.extractLsb'_xor]

theorem lo_and (x y : BitVec 64) : lo (x &&& y) = lo x &&& lo y := by
  simp [lo, BitVec.extractLsb'_and]

theorem hi_and (x y : BitVec 64) : hi (x &&& y) = hi x &&& hi y := by
  simp [hi, BitVec.extractLsb'_and]

theorem lo_or (x y : BitVec 64) : lo (x ||| y) = lo x ||| lo y := by
  simp [lo, BitVec.extractLsb'_or]

theorem hi_or (x y : BitVec 64) : hi (x ||| y) = hi x ||| hi y := by
  simp [hi, BitVec.extractLsb'_or]

/-! ## Rotations and shifts

The two parts of each half have no bits in common, so their exclusive or is
their or. -/

theorem lo_rotr {n : Nat} (x : BitVec 64) (h0 : 0 < n) (h : n < 32) :
    lo (x.rotateRight n) = lo x >>> n ^^^ hi x <<< (32 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [lo, hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight, BitVec.getLsbD_xor,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, Nat.mod_eq_of_lt (show n < 64 by omega)]
  by_cases hc : i < 32 - n
  · simp [hc, hi', show i < 64 - n by omega, show n + i < 32 by omega]
  · simp [hi', show i < 64 - n by omega, show ¬ n + i < 32 by omega, show ¬ i < 32 - n by omega,
      show i - (32 - n) < 32 by omega, show 32 + (i - (32 - n)) = n + i by omega]

theorem hi_rotr {n : Nat} (x : BitVec 64) (h0 : 0 < n) (h : n < 32) :
    hi (x.rotateRight n) = hi x >>> n ^^^ lo x <<< (32 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [lo, hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight, BitVec.getLsbD_xor,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, Nat.mod_eq_of_lt (show n < 64 by omega)]
  by_cases hc : i < 32 - n
  · simp [hc, hi', show 32 + i < 64 - n by omega, show n + i < 32 by omega,
      show n + (32 + i) = 32 + (n + i) by omega]
  · simp [show 32 + i < 64 by omega, hi', show ¬ 32 + i < 64 - n by omega,
      show ¬ n + i < 32 by omega, show ¬ i < 32 - n by omega, show i - (32 - n) < 32 by omega,
      show 32 + i - (64 - n) = i - (32 - n) by omega]

theorem lo_rotr' {n : Nat} (x : BitVec 64) (h0 : 32 < n) (h : n < 64) :
    lo (x.rotateRight n) = hi x >>> (n - 32) ^^^ lo x <<< (64 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [lo, hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight, BitVec.getLsbD_xor,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, Nat.mod_eq_of_lt h]
  by_cases hc : i < 64 - n
  · simp [hc, hi', show n - 32 + i < 32 by omega, show 32 + (n - 32 + i) = n + i by omega]
  · simp [show i < 64 by omega, hi', hc, show ¬ n - 32 + i < 32 by omega,
      show i - (64 - n) < 32 by omega]

theorem hi_rotr' {n : Nat} (x : BitVec 64) (h0 : 32 < n) (h : n < 64) :
    hi (x.rotateRight n) = lo x >>> (n - 32) ^^^ hi x <<< (64 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [lo, hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight, BitVec.getLsbD_xor,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, Nat.mod_eq_of_lt h]
  by_cases hc : i < 64 - n
  · simp [show 32 + i < 64 by omega, hc, hi', show n - 32 + i < 32 by omega,
      show ¬ 32 + i < 64 - n by omega, show 32 + i - (64 - n) = n - 32 + i by omega]
  · simp [show 32 + i < 64 by omega, hi', hc, show ¬ n - 32 + i < 32 by omega,
      show ¬ 32 + i < 64 - n by omega, show i - (64 - n) < 32 by omega,
      show 32 + i - (64 - n) = 32 + (i - (64 - n)) by omega]

theorem lo_shr {n : Nat} (x : BitVec 64) (h0 : 0 < n) (h : n < 32) :
    lo (x >>> n) = lo x >>> n ^^^ hi x <<< (32 - n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [lo, hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases hc : i < 32 - n
  · simp [hc, hi', show n + i < 32 by omega]
  · simp [hi', hc, show ¬ n + i < 32 by omega, show i - (32 - n) < 32 by omega,
      show 32 + (i - (32 - n)) = n + i by omega]

theorem hi_shr (n : Nat) (x : BitVec 64) : hi (x >>> n) = hi x >>> n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight]
  by_cases hc : n + i < 32
  · simp [hi', hc, show n + (32 + i) = 32 + (n + i) by omega]
  · simp [hi', hc]
    exact BitVec.getLsbD_of_ge x _ (by omega)

/-! ## The terms of `Σ₀`, `Σ₁`, `σ₀` and `σ₁` -/

/-- A term of `Σ₀`, `Σ₁`, `σ₀` or `σ₁`. -/
inductive Term
  /-- `ROTRⁿ` (`0 < n < 64`, `n ≠ 32`) -/
  | rotr (n : Nat)
  /-- `SHRⁿ` (`0 < n < 32`) -/
  | shr (n : Nat)
  deriving DecidableEq, Repr

/-- A term's value. -/
def Term.eval (x : BitVec 64) : Term → BitVec 64
  | .rotr n => x.rotateRight n
  | .shr n => x >>> n

/-- The shift amounts that the code can encode. -/
def Term.valid : Term → Bool
  | .rotr n => 0 < n && n < 64 && n != 32
  | .shr n => 0 < n && n < 32

/-- The exclusive or of the terms. -/
def evalOps (x : BitVec 64) (ops : List Term) : BitVec 64 := ops.foldl (fun a o => a ^^^ o.eval x) 0

/-- The values of the parts of a term's low half, from the halves `L`, `H`. -/
def Term.loVals (L H : BitVec 32) : Term → List (BitVec 32)
  | .rotr n => if n < 32 then [L >>> n, H <<< (32 - n)] else [H >>> (n - 32), L <<< (64 - n)]
  | .shr n => [L >>> n, H <<< (32 - n)]

/-- The values of the parts of a term's high half. -/
def Term.hiVals (L H : BitVec 32) : Term → List (BitVec 32)
  | .rotr n => if n < 32 then [H >>> n, L <<< (32 - n)] else [L >>> (n - 32), H <<< (64 - n)]
  | .shr n => [H >>> n]

theorem Term.lo_eval {o : Term} (hv : o.valid = true) (x : BitVec 64) :
    ((o.loVals (lo x) (hi x)).foldl (· ^^^ ·) 0) = lo (o.eval x) := by
  cases o with
  | rotr n =>
    simp only [Term.valid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hv
    simp only [Term.loVals, Term.eval]
    split
    · simp [lo_rotr x hv.1.1 (by omega)]
    · simp [lo_rotr' x (by omega) hv.1.2]
  | shr n =>
    simp only [Term.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp [Term.loVals, Term.eval, lo_shr x hv.1 hv.2]

theorem Term.hi_eval {o : Term} (hv : o.valid = true) (x : BitVec 64) :
    ((o.hiVals (lo x) (hi x)).foldl (· ^^^ ·) 0) = hi (o.eval x) := by
  cases o with
  | rotr n =>
    simp only [Term.valid, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hv
    simp only [Term.hiVals, Term.eval]
    split
    · simp [hi_rotr x hv.1.1 (by omega)]
    · simp [hi_rotr' x (by omega) hv.1.2]
  | shr n => simp [Term.hiVals, Term.eval, hi_shr]

theorem foldl_xor_acc (a : BitVec 32) (l : List (BitVec 32)) :
    l.foldl (· ^^^ ·) a = a ^^^ l.foldl (· ^^^ ·) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (0 ^^^ b)]
    simp [BitVec.xor_assoc]

theorem lo_evalOps (x : BitVec 64) (ops : List Term) (hv : ∀ o ∈ ops, o.valid = true) :
    (ops.flatMap (Term.loVals (lo x) (hi x))).foldl (· ^^^ ·) 0 = lo (evalOps x ops) := by
  suffices ∀ acc : BitVec 64, (ops.flatMap (Term.loVals (lo x) (hi x))).foldl (· ^^^ ·) (lo acc) =
      lo (ops.foldl (fun a o => a ^^^ o.eval x) acc) by
    simpa [evalOps, lo_zero] using this 0
  induction ops with
  | nil => intro; rfl
  | cons o os ih =>
    intro acc
    rw [List.flatMap_cons, List.foldl_append, List.foldl_cons,
      foldl_xor_acc (lo acc) (Term.loVals (lo x) (hi x) o), Term.lo_eval (hv o (by simp)), ← lo_xor]
    exact ih (fun o h => hv o (by simp [h])) _

theorem hi_evalOps (x : BitVec 64) (ops : List Term) (hv : ∀ o ∈ ops, o.valid = true) :
    (ops.flatMap (Term.hiVals (lo x) (hi x))).foldl (· ^^^ ·) 0 = hi (evalOps x ops) := by
  suffices ∀ acc : BitVec 64, (ops.flatMap (Term.hiVals (lo x) (hi x))).foldl (· ^^^ ·) (hi acc) =
      hi (ops.foldl (fun a o => a ^^^ o.eval x) acc) by
    simpa [evalOps, hi_zero] using this 0
  induction ops with
  | nil => intro; rfl
  | cons o os ih =>
    intro acc
    rw [List.flatMap_cons, List.foldl_append, List.foldl_cons,
      foldl_xor_acc (hi acc) (Term.hiVals (lo x) (hi x) o), Term.hi_eval (hv o (by simp)), ← hi_xor]
    exact ih (fun o h => hv o (by simp [h])) _

/-- The terms of `Σ₀`, `Σ₁`, `σ₀` and `σ₁`. -/
def bsig0 : List Term := [.rotr 28, .rotr 34, .rotr 39]
def bsig1 : List Term := [.rotr 14, .rotr 18, .rotr 41]
def ssig0 : List Term := [.rotr 1, .rotr 8, .shr 7]
def ssig1 : List Term := [.rotr 19, .rotr 61, .shr 6]

theorem bsig0_eq (x : BitVec 64) : Spec.Sha512.bsig0 x = evalOps x bsig0 := by
  simp [evalOps, bsig0, Spec.Sha512.bsig0, Term.eval]

theorem bsig1_eq (x : BitVec 64) : Spec.Sha512.bsig1 x = evalOps x bsig1 := by
  simp [evalOps, bsig1, Spec.Sha512.bsig1, Term.eval]

theorem ssig0_eq (x : BitVec 64) : Spec.Sha512.ssig0 x = evalOps x ssig0 := by
  simp [evalOps, ssig0, Spec.Sha512.ssig0, Term.eval]

theorem ssig1_eq (x : BitVec 64) : Spec.Sha512.ssig1 x = evalOps x ssig1 := by
  simp [evalOps, ssig1, Spec.Sha512.ssig1, Term.eval]

/-! ## Words in memory -/

theorem eq_of_bytes32 {x y : BitVec 32}
    (h : ∀ j < 4, x.extractLsb' (8 * j) 8 = y.extractLsb' (8 * j) 8) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := congrArg (fun z : BitVec 8 => z.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb'] at e
  simpa [Nat.mod_lt i (show 8 > 0 by omega), show 8 * (i / 8) + i % 8 = i by omega] using e

theorem readW_lo (m : Mem) (a : Addr) : lo (m.readW a 64) = m.readW a 32 := by
  apply eq_of_bytes32
  intro j hj
  rw [← Mem.readW_byte m a hj]
  have e := Mem.extractLsb'_read m a (n := 8) (j := j) (by omega)
  simp only [lo, Mem.readW] at e ⊢
  rw [← e]
  ext i hi
  simp [BitVec.getElem_extractLsb']
  omega

theorem readW_hi (m : Mem) (a : Addr) : hi (m.readW a 64) = m.readW (a + 4) 32 := by
  apply eq_of_bytes32
  intro j hj
  rw [← Mem.readW_byte m (a + 4) hj, show a + 4 + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (4 + j) by
    rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl]
  have e := Mem.extractLsb'_read m a (n := 8) (j := 4 + j) (by omega)
  simp only [hi, Mem.readW] at e ⊢
  rw [← e]
  ext i hi
  simp [BitVec.getElem_extractLsb', show 8 * j + i < 32 by omega,
    show 32 + (8 * j + i) = 8 * (4 + j) + i by omega]

/-- A 64-bit word in memory is its high half at `a + 4` and its low half at `a`. -/
theorem readW64 (m : Mem) (a : Addr) : m.readW a 64 = m.readW (a + 4) 32 ++ m.readW a 32 := by
  rw [← readW_lo m a, ← readW_hi m a, hi_append_lo]

/-! ## The message length -/

/-- The big-endian bytes of a 64-bit word are those of its high half, then
those of its low half. -/
theorem wordBytes_split (x : BitVec 64) :
    Spec.Sha512.wordBytes x = Spec.Sha256.wordBytes (hi x) ++ Spec.Sha256.wordBytes (lo x) := by
  simp only [Spec.Sha512.wordBytes, Spec.Sha256.wordBytes, List.range_succ, List.range_zero, List.nil_append,
    List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.cons.injEq, and_true, hi, lo]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i hi
  all_goals simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  all_goals rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega

theorem lo_shr61 (x : BitVec 64) : lo (x >>> 61) = hi x >>> 29 := by
  apply BitVec.eq_of_toNat_eq
  rw [lo_toNat]
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hi_toNat]
  have := x.isLt
  omega

theorem hi_shr61 (x : BitVec 64) : hi (x >>> 61) = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [hi_toNat]
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (0 : BitVec 32).toNat = 0 from rfl]
  have := x.isLt
  omega

theorem lo_shl3 (x : BitVec 64) : lo (x <<< 3) = lo x <<< 3 := by
  apply BitVec.eq_of_toNat_eq
  rw [lo_toNat]
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, lo_toNat]
  omega

theorem hi_shl3 (x : BitVec 64) : hi (x <<< 3) = (hi x <<< 3) ||| (lo x >>> 29) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [hi, lo, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, hi', decide_true, Bool.true_and]
  by_cases h : i < 3
  · rw [decide_eq_true (by omega : 32 + i < 64), decide_eq_false (by omega : ¬ 32 + i < 3),
      decide_eq_true (by omega : 29 + i < 32), show 32 + i - 3 = 29 + i by omega]
    rw [decide_eq_true h, Nat.zero_add]
    simp only [Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or]
  · rw [decide_eq_true (by omega : 32 + i < 64), decide_eq_false (by omega : ¬ 32 + i < 3),
      decide_eq_true (by omega : i - 3 < 32), decide_eq_false (by omega : ¬ 29 + i < 32),
      show 32 + i - 3 = 32 + (i - 3) by omega]
    rw [decide_eq_false h]
    simp only [Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false]

end VG.Proof.Sha512.Word64
