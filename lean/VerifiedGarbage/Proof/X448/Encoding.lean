import VerifiedGarbage.Proof.X448.Pairs

/-!
# X448: encoding pairs of limbs

Seven output bytes encode two bounded limbs, and eight such pairs encode the
complete field element.
-/

namespace VG.Proof.X448

open VG VG.Spec.X448
open VG.Proof.X25519 (leNum leBytes)

theorem leNum_leBytes {n x : Nat} (hx : x < 256 ^ n) : leNum (leBytes n x) = x := by
  induction n generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    subst x
    rfl
  | succ n ih =>
    rw [VG.Proof.X25519.leBytes_succ, leNum, ih (by
      apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
      simpa only [Nat.pow_succ, Nat.mul_comm] using hx)]
    exact Nat.mod_add_div x 256

theorem decoded_packed {m : Mem} {p : Addr} {f : Nat → Nat} (hf : ∀ i < 16, f i < radix)
    (hc : ∀ i < 8, chunk m p i = f (2 * i) + radix * f (2 * i + 1)) :
    ∀ i < 16, decoded m p i = f i := by
  intro i hi
  have h := hc (i / 2) (by omega)
  have h0 := hf (2 * (i / 2)) (by omega)
  have h1 : radix = 268435456 := rfl
  unfold decoded
  rw [h]
  split
  · rename_i he
    have e : 2 * (i / 2) = i := by omega
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0, e]
  · rename_i he
    have e : 2 * (i / 2) + 1 = i := by omega
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt h0, Nat.zero_add, e]

theorem packed_bytes {m : Mem} {p : Addr} {f : Nat → Nat} (hf : ∀ i < 16, f i < radix)
    (hc : ∀ i < 8, chunk m p i = f (2 * i) + radix * f (2 * i + 1)) :
    bytesAt m p 56 = leBytes 56 (valN f 16) := by
  have hv : leNum (bytesAt m p 56) = valN f 16 :=
    (decoded_val m p 8).symm.trans (valN_congr (decoded_packed hf hc))
  have out : bytesAt m p 56 = leBytes 56 (m.read p 56).toNat :=
    VG.Proof.X25519.bytesAt_leBytes m p 56
  rw [← leNum_bytesAt_read, hv] at out
  exact out

end VG.Proof.X448
