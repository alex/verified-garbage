import VerifiedGarbage.Spec.Ct
import VerifiedGarbage.Proof.Framework.Mem

/-! Target-independent facts relating bytewise comparison to the complete spec. -/
namespace VG.Proof.Ct
open VG

theorem or_zero (x y : Byte) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := BitVec.or_eq_zero_iff
theorem xor_zero (x y : Byte) : x ^^^ y = 0 ↔ x = y := BitVec.xor_eq_zero_iff

def diff (m : Mem) (a b : Addr) : Nat → Byte
  | 0 => 0
  | n + 1 => diff m a b n ||| (m (a + BitVec.ofNat 64 n) ^^^ m (b + BitVec.ofNat 64 n))

theorem diff_zero (m : Mem) (a b : Addr) (n : Nat) :
    diff m a b n = 0 ↔ ∀ i < n, m (a + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i) := by
  induction n with
  | zero => simp [diff]
  | succ n ih =>
    rw [diff, or_zero, xor_zero, ih, Nat.forall_lt_succ_right]

theorem diff_spec (m : Mem) (a b : Addr) (n : Nat) :
    Spec.Ct.eq (Spec.Ct.bytesAt m a n) (Spec.Ct.bytesAt m b n) = decide (diff m a b n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Spec.Ct.eq, beq_iff_eq, decide_eq_true_eq, diff_zero, Spec.Ct.bytesAt]
  rw [List.map_inj_left]
  simp only [List.mem_range]

theorem lengths_ne (m : Mem) (a b : Addr) {n k : Nat} (h : n ≠ k) :
    Spec.Ct.eq (Spec.Ct.bytesAt m a n) (Spec.Ct.bytesAt m b k) = false := by
  simp only [Spec.Ct.eq, beq_eq_false_iff_ne]
  intro he
  have := congrArg List.length he
  simp only [Spec.Ct.bytesAt, List.length_map, List.length_range] at this
  exact h this

theorem result64 (d : Byte) :
    (((d.setWidth 64 - 1) >>> 63).setWidth 32) = if d = 0 then 1 else 0 := by
  have h : ∀ d : Byte, (((d.setWidth 64 - 1) >>> 63).setWidth 32) =
      if d = 0 then 1 else 0 := by decide +kernel
  exact h d
end VG.Proof.Ct
