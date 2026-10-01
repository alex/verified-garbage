import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Extend

/-! # H′: emitting the complete short or long output -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_cmpi)
open VG.Spec.Blake2 (bytesAt)

theorem finishOutput_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (n : Nat) (input : List Byte)
    (space : Space s n) (positive : 1 ≤ n) (count : s.gpr .r15 = BitVec.ofNat 64 n)
    (digest : (bytesAt s.mem (s.gpr .rbx + 768) 64).take (min n 64) =
      Spec.Argon2.H (min n 64) (Spec.Argon2.le32 n ++ input)) :
    WP isa (finishOutput (hash v)) s (Written s (Spec.Argon2.hPrime n input)) := by
  unfold finishOutput
  refine WP.seq (wp_cmpi fun u gu mu ru wu cf _ => WP.block_nil ?_)
  have ku : Keeps s u := ⟨fun r _ => congrFun gu r, ru, wu, by rw [mu]; exact Frame.refl _ _⟩
  have countU : u.gpr .r15 = BitVec.ofNat 64 n := (congrFun gu _).trans count
  have cfU : u.cf = some (decide (n < 65)) := by
    rw [cf, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt space.bound]; rfl
  apply WP.seq
  refine WP.ite (decide (n < 65)) (by simp only [eval, cfU]) ?_ ?_
  · intro h
    have short : n ≤ 64 := by have := of_decide_eq_true h; omega
    apply WP.block_nil
    refine (copyRemaining_ok u n (space.keeps ku) positive short countU).mono ?_
    intro t ht
    have result := ht.before_keeps ku
    have value : bytesAt u.mem (u.gpr .rbx + 768) n = Spec.Argon2.hPrime n input := by
      rw [mu, gu, ← bytesAt_take _ _ n 64 short]
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
    have countLong : u.gpr .r15 = BitVec.ofNat 64 (32 * (q + 1) + lastLen) := by rw [size]; exact countU
    apply WP.seq_iff.mp
    refine (longOutput_ok v q lastLen u spaceU ⟨bounds.2.1, bounds.2.2.1⟩ countLong).mono ?_
    intro t ht
    have result := ht.before_keeps ku
    have digestU : bytesAt u.mem (u.gpr .rbx + 768) 64 =
        Spec.Argon2.H 64 (Spec.Argon2.le32 n ++ input) := by
      rw [mu, gu]
      simpa only [Nat.min_eq_right (show 64 ≤ n by omega), bytesAt_take _ _ 64 64 (by decide)] using digest
    have value : Spec.Argon2.longHash lastLen (q + 1) (bytesAt u.mem (u.gpr .rbx + 768) 64) =
        Spec.Argon2.hPrime n input := by
      rw [digestU, ← hq, Spec.Argon2.hPrime, ite_eq_right (show ¬ n ≤ 64 by omega)]
    rw [value] at result
    exact result

end VG.Proof.Argon2.X86_64.HPrime
