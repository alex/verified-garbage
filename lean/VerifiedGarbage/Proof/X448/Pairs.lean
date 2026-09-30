import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.Limbs

/-!
# X448: seven-byte chunks and limb pairs

Untrusted: everything here is checked by Lean. A seven-byte chunk contains
exactly two 28-bit limbs. Reading eight chunks uses all 56 input bytes.
-/

namespace VG.Proof.X448

open VG VG.Spec.X448
open VG.Proof.X25519 (leNum leNum_append leNum_lt)

abbrev chunk (m : Mem) (p : Addr) (i : Nat) : Nat :=
  leNum (bytesAt m (p + BitVec.ofNat 64 (7 * i)) 7)

def decoded (m : Mem) (p : Addr) (i : Nat) : Nat :=
  if i % 2 = 0 then chunk m p (i / 2) % radix else chunk m p (i / 2) / radix

theorem chunk_lt (m : Mem) (p : Addr) (i : Nat) : chunk m p i < radix * radix := by
  have h := leNum_lt (bytesAt m (p + BitVec.ofNat 64 (7 * i)) 7)
  rw [length_bytesAt] at h
  exact h

theorem decoded_even (m : Mem) (p : Addr) (i : Nat) : decoded m p (2 * i) = chunk m p i % radix := by
  rw [decoded, show 2 * i % 2 = 0 by omega, ite_eq_left rfl, show 2 * i / 2 = i by omega]

theorem decoded_odd (m : Mem) (p : Addr) (i : Nat) : decoded m p (2 * i + 1) = chunk m p i / radix := by
  have hd : (2 * i + 1) / 2 = i := by omega
  have hm : (2 * i + 1) % 2 = 1 := by omega
  rw [decoded, hd, hm, ite_eq_right (by decide)]

theorem decoded_bound (m : Mem) (p : Addr) (i : Nat) : decoded m p i < radix := by
  unfold decoded
  split
  · exact Nat.mod_lt _ (by decide)
  · have h := chunk_lt m p (i / 2)
    exact (Nat.div_lt_iff_lt_mul (by decide)).mpr h

theorem byte_power (n : Nat) : 256 ^ (7 * n) = radix ^ (2 * n) := by
  rw [Nat.pow_mul, Nat.pow_mul]
  exact congrArg (fun b => b ^ n) (by decide)

theorem decoded_val (m : Mem) (p : Addr) (n : Nat) :
    valN (decoded m p) (2 * n) = leNum (bytesAt m p (7 * n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, valN, valN, ih, decoded_even, decoded_odd,
      Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, Nat.mod_add_div]
    rw [show 7 * (n + 1) = 7 * n + 7 by omega, bytesAt_add, leNum_append, length_bytesAt, byte_power]

/-- Accumulating a seven-byte chunk from its highest byte downwards. -/
def suffix (m : Mem) (p : Addr) (i n : Nat) : Nat :=
  leNum (bytesAt m (p + BitVec.ofNat 64 (7 * i + (7 - n))) n)

theorem suffix_bound (m : Mem) (p : Addr) (i n : Nat) : suffix m p i n < 256 ^ n := by
  have h := leNum_lt (bytesAt m (p + BitVec.ofNat 64 (7 * i + (7 - n))) n)
  rw [length_bytesAt] at h
  exact h

theorem suffix_succ (m : Mem) (p : Addr) (i : Nat) {n : Nat} (hn : n < 7) :
    suffix m p i (n + 1) = 256 * suffix m p i n + (m (p + BitVec.ofNat 64 (7 * i + (6 - n)))).toNat := by
  unfold suffix
  have bs : ∀ (q : Addr) (n : Nat), bytesAt m q (n + 1) = m q :: bytesAt m (q + 1) n :=
    VG.Proof.X25519.bytesAt_succ m
  rw [bs, leNum]
  have he : p + BitVec.ofNat 64 (7 * i + (7 - (n + 1))) + 1 =
      p + BitVec.ofNat 64 (7 * i + (7 - n)) := by
    change p + BitVec.ofNat 64 (7 * i + (7 - (n + 1))) + BitVec.ofNat 64 1 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [he, show 7 - (n + 1) = 6 - n by omega, Nat.add_comm]

end VG.Proof.X448
