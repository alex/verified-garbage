import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Spec.Sha3.Contract

/-!
# The SHA-3 sponge: arithmetic and bytes, for every target

Untrusted: everything here is checked by Lean. Facts about counters, byte
stores and the rates that the streaming proofs of every target use.
-/

namespace VG.Proof.Sha3

open VG.Spec.Sha3 (bytesAt rates)

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, ofNat_succ, Nat.add_sub_cancel, BitVec.add_sub_cancel]

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  conv_lhs => rw [show a = (a - b) + b by omega, BitVec.ofNat_add]
  rw [BitVec.add_sub_cancel]

theorem ofNat_beq_zero{k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

theorem xor_setWidth (x y : Byte) : (x.setWidth 64 ^^^ y.setWidth 64).setWidth 8 = x ^^^ y := by
  ext i hi
  simp

/-- A one-byte store. -/
theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    m.writeW a v x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h
    simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero, ite_true]
    ext i hi
    simp
  · have : ¬ (x - a).toNat < 8 / 8 := by bv_omega
    simp only [this, h, ite_false]

theorem bytesAt_succ (m : Mem) (p : Addr) (c : Nat) :
    bytesAt m p (c + 1) = bytesAt m p c ++ [m (p + BitVec.ofNat 64 c)] := by
  simp [bytesAt, List.range_succ]

theorem bytesAt_length (m : Mem) (p : Addr) (c : Nat) : (bytesAt m p c).length = c := by
  simp [bytesAt]

theorem rate_bounds {r : Nat} (h : r ∈ rates) : 72 ≤ r ∧ r ≤ 168 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem ne_of_lt200 {p : Addr} {a b : Nat} (ha : a < 200) (hb : b < 200) (h : a ≠ b) :
    p + BitVec.ofNat 64 a ≠ p + BitVec.ofNat 64 b := by
  intro e; apply h; bv_omega

theorem beq_zero (x : BitVec 64) : (x == 0) = decide (x.toNat = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    rw [beq_eq_false_iff_ne.mpr h]; simp [this]

theorem sub_beq_zero {a : Nat} (ha : a < 2 ^ 64) (y : BitVec 64) :
    (BitVec.ofNat 64 a - y == 0) = decide (a = y.toNat) := by
  by_cases h : a = y.toNat
  · subst h; simp
  · have : BitVec.ofNat 64 a - y ≠ 0 := by intro e; apply h; bv_omega
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem xor_byte (b : BitVec 8) (v : BitVec 64) :
    (b.setWidth 64 ^^^ v).setWidth 8 = b ^^^ v.setWidth 8 := by
  ext i _; simp

theorem writeW8_self (m : Mem) (a : Addr) (v : BitVec 8) : (m.writeW a v) a = v := by
  simp [Mem.writeW, Mem.write]

theorem writeW8_other (m : Mem) {a x : Addr} (v : BitVec 8) (h : x ≠ a) : (m.writeW a v) x = m x :=
  Mem.write_apply (by intro h'; apply h; bv_omega)

theorem div_mod_eq {r k pos : Nat} (hr : 0 < r) (hlt : pos < r) :
    (r * k + pos) / r = k ∧ (r * k + pos) % r = pos := by
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_div hr, Nat.div_eq_of_lt hlt, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

end VG.Proof.Sha3
