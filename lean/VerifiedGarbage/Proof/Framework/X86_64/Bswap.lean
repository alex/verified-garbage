import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.TCB.X86_64.Isa
import Mathlib.Tactic.SplitIfs

/-!
# `bswap` of a little-endian load is a big-endian load

Untrusted: everything here is checked by Lean.
-/

namespace VG.X86_64

theorem getLsbD_cat4 (b0 b1 b2 b3 : BitVec 8) (i : Nat) :
    (b0 ++ b1 ++ b2 ++ b3 : BitVec (8 + 8 + 8 + 8)).getLsbD i =
      if i < 8 then b3.getLsbD i else if i < 16 then b2.getLsbD (i - 8)
      else if i < 24 then b1.getLsbD (i - 16) else b0.getLsbD (i - 24) := by
  simp only [BitVec.getLsbD_append]
  split_ifs <;> first | omega | rfl

/-- The low byte of `y ++ a`. -/
theorem extractLsb'_append_byte_lo {w : Nat} (y : BitVec w) (a : BitVec 8) :
    (y ++ a).extractLsb' 0 8 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_append, hi]

/-- A byte of `y ++ a` above the low one. -/
theorem extractLsb'_append_byte_hi {w : Nat} (y : BitVec w) (a : BitVec 8) {k : Nat} (hk : 8 ≤ k) :
    (y ++ a).extractLsb' k 8 = y.extractLsb' (k - 8) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬k + i < 8 by omega, ite_false]
  exact congrArg _ (by omega)

theorem bswap32_bytes (b0 b1 b2 b3 : BitVec 8) :
    bswap32 ((0#0 ++ b3 ++ b2 ++ b1 ++ b0).setWidth 32) = (b0 ++ b1 ++ b2 ++ b3 : BitVec 32) := by
  simp (disch := decide) only [bswap32, BitVec.setWidth_eq, extractLsb'_append_byte_hi,
    extractLsb'_append_byte_lo, Nat.reduceSub]

/-- A 32-bit load followed by `bswap` reads the four bytes big-endian. -/
theorem bswap32_readW (m : Mem) (a : Addr) :
    bswap32 (m.readW a 32) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) : BitVec 32) :=
  bswap32_bytes _ _ _ _

theorem getLsbD_cat8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (i : Nat) :
    (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 :
        BitVec (8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)).getLsbD i =
      if i < 8 then b7.getLsbD i else if i < 16 then b6.getLsbD (i - 8)
      else if i < 24 then b5.getLsbD (i - 16) else if i < 32 then b4.getLsbD (i - 24)
      else if i < 40 then b3.getLsbD (i - 32) else if i < 48 then b2.getLsbD (i - 40)
      else if i < 56 then b1.getLsbD (i - 48) else b0.getLsbD (i - 56) := by
  simp only [BitVec.getLsbD_append]
  simp only [Nat.sub_sub, Nat.reduceAdd]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨
    (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ 56 ≤ i) with
    h | h | h | h | h | h | h | h <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right]

theorem bswap64_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    bswap64 ((0#0 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).setWidth 64) =
      (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) := by
  simp (disch := decide) only [bswap64, BitVec.setWidth_eq, extractLsb'_append_byte_hi,
    extractLsb'_append_byte_lo, Nat.reduceSub]

/-- A 64-bit load followed by `bswap` reads the eight bytes big-endian. -/
theorem bswap64_readW (m : Mem) (a : Addr) :
    bswap64 (m.readW a 64) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) ++
      m (a + 1 + 1 + 1 + 1) ++ m (a + 1 + 1 + 1 + 1 + 1) ++ m (a + 1 + 1 + 1 + 1 + 1 + 1) ++
      m (a + 1 + 1 + 1 + 1 + 1 + 1 + 1) : BitVec 64) :=
  bswap64_bytes _ _ _ _ _ _ _ _

end VG.X86_64
