import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Extend

/-! # H′: emitting the complete short or long output -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem finishOutput_ok (v : Backend) (s : State) (n : Nat) (input : List Byte)
    (space : Space s n) (positive : 1 ≤ n) (count : s.gpr .x23 = BitVec.ofNat 64 n)
    (digest : (bytesAt s.mem (s.gpr .x24 + 768) 64).take (min n 64) =
      Spec.Argon2.H (min n 64) (Spec.Argon2.le32 n ++ input)) :
    WP isa (finishOutput v.hash) s (Written s (Spec.Argon2.hPrime n input)) := by
  unfold finishOutput
  refine WP.seq ((compare_ok s (by rw [count, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := space.bound; omega)]; exact space.bound)).mono fun u compared => ?_)
  have ku := compared.keeps
  have countU : u.gpr .x23 = BitVec.ofNat 64 n := (compared.other _ (by decide)).trans count
  have compareU : u.gpr .x9 = if n < 65 then 1 else 0 := by
    rw [compared.value, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := space.bound; omega)]
  apply WP.seq
  refine WP.ite (decide (n < 65)) (by by_cases h : n < 65 <;> simp [eval, State.read, compareU, h]) ?_ ?_
  · intro h
    have short : n ≤ 64 := by have := of_decide_eq_true h; omega
    apply WP.block_nil
    refine (copyRemaining_ok u n (space.keeps ku) positive short countU).mono ?_
    intro t ht
    have result := ht.before_keeps ku
    have value : bytesAt u.mem (u.gpr .x24 + 768) n = Spec.Argon2.hPrime n input := by
      rw [compared.mem, ku.x24, ← bytesAt_take _ _ n 64 short]
      simpa only [Nat.min_eq_left short, Spec.Argon2.hPrime, ite_eq_left short] using digest
    rw [value] at result
    exact result
  · intro h
    have long : 64 < n := by have := of_decide_eq_false h; omega
    let r := (n + 31) / 32 - 2
    let lastLen := n - 32 * r
    have bounds : 1 ≤ r ∧ 33 ≤ lastLen ∧ lastLen ≤ 64 ∧ 32 * r + lastLen = n :=
      Proof.Argon2.longHash_bounds n long
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
    change r = q + 1 at hq
    have size : 32 * (q + 1) + lastLen = n := by rw [← hq]; exact bounds.2.2.2
    have spaceU : Space u (32 * (q + 1) + lastLen) := by rw [size]; exact space.keeps ku
    have countLong : u.gpr .x23 = BitVec.ofNat 64 (32 * (q + 1) + lastLen) := by rw [size]; exact countU
    apply WP.seq_iff.mp
    refine (longOutput_ok v q lastLen u spaceU ⟨bounds.2.1, bounds.2.2.1⟩ countLong).mono ?_
    intro t ht
    have result := ht.before_keeps ku
    have digestU : bytesAt u.mem (u.gpr .x24 + 768) 64 =
        Spec.Argon2.H 64 (Spec.Argon2.le32 n ++ input) := by
      rw [compared.mem, ku.x24]
      simpa only [Nat.min_eq_right (show 64 ≤ n by omega), bytesAt_take _ _ 64 64 (by decide)] using digest
    have value : Spec.Argon2.longHash lastLen (q + 1) (bytesAt u.mem (u.gpr .x24 + 768) 64) =
        Spec.Argon2.hPrime n input := by
      rw [digestU, ← hq, Spec.Argon2.hPrime, ite_eq_right (show ¬ n ≤ 64 by omega)]
    rw [value] at result
    exact result

end VG.Proof.Argon2.AArch64.HPrime
