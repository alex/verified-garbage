import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarByte
import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Scalar reduction: the 64-byte loop

Untrusted. The invariant is the value modulo L of the already consumed
suffix of the little-endian input. The body writes no memory.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Spec.Ed25519 (L bytesAt decodeLE)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

theorem suffix_step (m : Mem) (p : Addr) (n : Nat) (hn : n < 64) :
    decodeLE ((bytesAt m p 64).drop n) % L =
      (256 * (decodeLE ((bytesAt m p 64).drop (n + 1)) % L) +
        (m (p + BitVec.ofNat 64 n)).toNat) % L := by
  rw [List.drop_eq_getElem_cons (by rw [bytesAt_length]; exact hn), reduce_cons]
  simp only [bytesAt, List.getElem_map, List.getElem_range]

theorem scalar_counter_test : ∀ n < 64,
    (BitVec.ofNat 64 n != 0) = decide (n ≠ 0) := by decide

structure ScalarInv (s₀ : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 64
  counter : s.gpr .x19 = BitVec.ofNat 64 n
  value : scalarValue s = decodeLE ((bytesAt s₀.mem (s₀.gpr .x1) 64).drop n) % L
  keeps : Keeps scalarBodyClob s₀ s

theorem scalarLoop_ok (s₀ : State) (hb : s₀.gpr .x19 = 64) (hz : scalarValue s₀ = 0)
    (hr : ∀ n < 64, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + BitVec.ofNat 64 n) 1)
    (hz0 : s₀.gpr .x10 = 0) (h1 : s₀.gpr .x11 = 1) :
    WP isa (.loop (.block scalarByte) (.nonzero .x .x19)) s₀ fun t =>
      scalarValue t = decodeLE (bytesAt s₀.mem (s₀.gpr .x1) 64) % L ∧
      Keeps scalarBodyClob s₀ t := by
  apply WP.loop (ScalarInv s₀) (n := 64)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 64 := by have := hi.bound; omega
    have hp : s.gpr .x1 = s₀.gpr .x1 := hi.keeps.gpr .x1 (by decide)
    have hread : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 k) 1 := by
      rw [hi.keeps.rd, hi.keeps.wr, hp]; exact hr k hk
    have hv : scalarValue s < L := by rw [hi.value]; exact Nat.mod_lt _ order_pos
    have hzs := (hi.keeps.gpr .x10 (by decide)).trans hz0
    have h1s := (hi.keeps.gpr .x11 (by decide)).trans h1
    refine WP.mono (scalarByte_ok s k hi.counter hread hv hzs h1s) fun t ⟨htb, htv, htk⟩ => ?_
    have kt := hi.keeps.trans htk
    have vt : scalarValue t = decodeLE ((bytesAt s₀.mem (s₀.gpr .x1) 64).drop k) % L := by
      rw [htv, hi.value, hp, hi.keeps.mem, suffix_step _ _ k hk]
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, read_x, htb, scalar_counter_test 0 (by decide), show decide ((0 : Nat) ≠ 0) = false from rfl],
        by simpa only [List.drop_zero] using vt, kt⟩
    · exact Or.inr ⟨by simp only [eval, read_x, htb, scalar_counter_test k hk, decide_eq_true hk0],
        k, by omega, ⟨by omega, by omega, htb, vt, kt⟩⟩
  · refine ⟨by decide, by decide, hb, ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
    rw [hz, List.drop_eq_nil_of_le (by rw [bytesAt_length])]
    rfl

end VG.Proof.Ed25519.AArch64
