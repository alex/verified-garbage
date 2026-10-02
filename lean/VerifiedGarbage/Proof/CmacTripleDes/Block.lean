import VerifiedGarbage.Proof.CmacTripleDes.Des
import VerifiedGarbage.Proof.Framework.Mem

/-!
# TDEA: the passes, and the key schedule in memory

Untrusted: everything here is checked by Lean.

`des` is `IP`, sixteen rounds and `IP⁻¹`; TDEA's three passes share one
`IP` and one `IP⁻¹`, which cancel between them, so that the passes are the
rounds with the halves exchanged (`tdes_eq`). The key schedule's slots are
little-endian words (`scheduleAt_getD`).
-/

namespace VG.Proof.CmacTripleDes

open VG Spec.TripleDes

theorem vgetD {α : Type} {n : Nat} (xs : Vector α n) {i : Nat} (h : i < n) (d : α) :
    xs.getD i d = xs[i] := by
  simp [Vector.getD, Array.getD, h]

/-! ## Words in memory -/

/-- Bit `i` of a little-endian word is bit `i % 8` of its byte `i / 8`. -/
theorem getLsbD_readW64 (m : Mem) (a : Addr) {i : Nat} (hi : i < 64) :
    (m.readW a 64).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8) := by
  rw [← Mem.extractLsb'_read m a (n := 8) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    show i % 8 < 8 from Nat.mod_lt _ (by decide)]
  congr 1; omega

theorem getLsbD_bytes_prefix (f : Nat → Byte) (k i : Nat) (hi : i < 64) :
    ((List.range k).foldl (fun (out : BitVec 64) j => out ||| (f j).zeroExtend 64 <<< (8 * j)) 0).getLsbD i =
      (decide (i < 8 * k) && (f (i / 8)).getLsbD (i % 8)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, BitVec.getLsbD_or, ih,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases h : i < 8 * k
    · simp [h, show i < 8 * (k + 1) by omega]
    · by_cases h' : i < 8 * (k + 1)
      · have e : i / 8 = k := by omega
        simp [h, h', hi, show i - 8 * k = i % 8 by omega, e, show i % 8 < 64 by omega]
      · simp only [h, h', decide_false, Bool.false_and, Bool.false_or, hi, decide_true,
          Bool.true_and]
        rw [BitVec.getLsbD_of_ge _ _ (by omega)]
        simp

/-- Slot `n` of the key schedule is the word at `p + 8 n`. -/
theorem scheduleAt_getD (m : Mem) (p : Addr) {n : Nat} (hn : n < 48) :
    (scheduleAt m p).getD n 0 = m.readW (p + BitVec.ofNat 64 (8 * n)) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [vgetD _ hn, scheduleAt, Vector.getElem_ofFn, getLsbD_bytes_prefix _ 8 i hi,
    getLsbD_readW64 _ _ hi, decide_eq_true hi, Bool.true_and, BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## Rounds -/

/-- Rounds `0 … n - 1` from the halves `(L, R)`, with the round keys `ks`. -/
def rounds (ks : Nat → BitVec 48) (n : Nat) (lr : BitVec 32 × BitVec 32) : BitVec 32 × BitVec 32 :=
  (List.range n).foldl (fun lr j => (lr.2, lr.1 ^^^ roundFunction lr.2 (ks j))) lr

theorem rounds_succ (ks : Nat → BitVec 48) (n : Nat) (lr : BitVec 32 × BitVec 32) :
    rounds ks (n + 1) lr =
      ((rounds ks n lr).2, (rounds ks n lr).1 ^^^ roundFunction (rounds ks n lr).2 (ks n)) := by
  simp only [rounds, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The round keys of `des keys dir`, in the order it uses them. -/
def keyOrder (keys : DesSchedule) (dir : Direction) (j : Nat) : BitVec 48 :=
  keys.getD (if dir = .encrypt then j else 15 - j) 0

/-- The halves `(L, R)` of a block. -/
def split (x : BitVec 64) : BitVec 32 × BitVec 32 := ((x >>> 32).setWidth 32, x.setWidth 32)

theorem des_eq (keys : DesSchedule) (dir : Direction) (x : BitVec 64) :
    des keys dir x =
      permute fp ((rounds (keyOrder keys dir) 16 (split (permute ip x))).2 ++
        (rounds (keyOrder keys dir) 16 (split (permute ip x))).1) := by
  have h : (fun (lr : BitVec 32 × BitVec 32) (j : Nat) =>
      match lr with
      | (l, r) =>
        let k := keys.getD (if dir = .encrypt then j else 15 - j) 0
        (r, l ^^^ roundFunction r k)) =
      fun lr j => (lr.2, lr.1 ^^^ roundFunction lr.2 (keyOrder keys dir j)) := by
    funext lr j; rfl
  simp only [des, h]
  rfl

theorem ip_fp (x : BitVec 64) : permute ip (permute fp x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h : ∀ j < 64, 64 - ip.getD (64 - 1 - j) 1 < 64 ∧
      64 - fp.getD (64 - 1 - (64 - ip.getD (64 - 1 - j) 1)) 1 = j := by decide
  rw [getLsbD_permute _ _ (by decide) hj, getLsbD_permute _ _ (by decide) (h j hj).1, (h j hj).2]

theorem split_append (r l : BitVec 32) : split (r ++ l) = (r, l) := by
  simp only [split, Prod.mk.injEq]
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
      ite_eq_right (by omega), Nat.add_sub_cancel_left, decide_eq_true hi, Bool.true_and]
  · rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, ite_eq_left hi, decide_eq_true hi, Bool.true_and]

/-! ## TDEA -/

/-- `(L, R)` exchanged. -/
def swap (lr : BitVec 32 × BitVec 32) : BitVec 32 × BitVec 32 := (lr.2, lr.1)

/-- The round keys of TDEA's pass `p` (`E_K1`, `D_K2`, `E_K3`). -/
def passKeys (S : Schedule) (p : Nat) : Nat → BitVec 48 :=
  keyOrder (componentSchedule S p) (if p % 2 = 1 then .decrypt else .encrypt)

/-- The halves after `p` passes (the halves exchanged after each). -/
def passes (S : Schedule) : Nat → BitVec 32 × BitVec 32 → BitVec 32 × BitVec 32
  | 0, lr => lr
  | p + 1, lr => swap (rounds (passKeys S p) 16 (passes S p lr))

/-- TDEA encryption (`E_K3(D_K2(E_K1(x)))`) of a 64-bit block. -/
def tdes (S : Schedule) (x : BitVec 64) : BitVec 64 :=
  des (componentSchedule S 2) .encrypt (des (componentSchedule S 1) .decrypt
    (des (componentSchedule S 0) .encrypt x))

/-- TDEA encryption of a 64-bit block: `IP`, the passes, `IP⁻¹`. -/
theorem tdes_eq (S : Schedule) (x : BitVec 64) :
    tdes S x =
      permute fp ((passes S 3 (split (permute ip x))).1 ++ (passes S 3 (split (permute ip x))).2) := by
  simp only [tdes, des_eq, ip_fp, split_append, passes, passKeys, swap]
  rfl

/-- Pass `p`'s round key `j` is the low 48 bits of slot `kpos p j`. -/
theorem passKeys_eq (S : Schedule) {p j : Nat} (hj : j < 16) :
    passKeys S p j = (S.getD (16 * p + if p % 2 = 1 then 15 - j else j) 0).setWidth 48 := by
  simp only [passKeys, keyOrder, componentSchedule]
  split <;> split <;> simp_all <;> rw [vgetD _ (by omega), Vector.getElem_ofFn]

end VG.Proof.CmacTripleDes
