import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarByte
import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Scalar reduction: the 64-byte loop

Untrusted. The invariant is the value modulo L of the already consumed
suffix of the little-endian input. The body writes no memory.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps)
open VG.Spec.Ed25519 (L bytesAt decodeLE)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

theorem suffix_step (m : Mem) (p : Addr) (n : Nat) (hn : n < 64) :
    decodeLE ((bytesAt m p 64).drop n) % L =
      (256 * (decodeLE ((bytesAt m p 64).drop (n + 1)) % L) +
        (m (p + BitVec.ofNat 64 n)).toNat) % L := by
  rw [List.drop_eq_getElem_cons (by rw [bytesAt_length]; exact hn), reduce_cons]
  simp only [bytesAt, List.getElem_map, List.getElem_range]

structure ScalarInv (s₀ : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 64
  counter : s.gpr .rbx = BitVec.ofNat 64 n
  value : scalarValue s = decodeLE ((bytesAt s₀.mem (s₀.gpr .rsi) 64).drop n) % L
  keeps : Keeps scalarBodyClob s₀ s

theorem scalarLoop_ok (s₀ : State) (hb : s₀.gpr .rbx = 64) (hz : scalarValue s₀ = 0)
    (hr : ∀ n < 64, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 n) 1) :
    WP isa (.loop (.block scalarByte) .ne) s₀ fun t =>
      scalarValue t = decodeLE (bytesAt s₀.mem (s₀.gpr .rsi) 64) % L ∧
      Keeps scalarBodyClob s₀ t := by
  apply WP.loop (ScalarInv s₀) (n := 64)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 64 := by have := hi.bound; omega
    have hp : s.gpr .rsi = s₀.gpr .rsi := hi.keeps.1 .rsi (by decide)
    have hread : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 k) 1 := by
      rw [hi.keeps.2.2.1, hi.keeps.2.2.2, hp]; exact hr k hk
    have hv : scalarValue s < L := by rw [hi.value]; exact Nat.mod_lt _ order_pos
    refine WP.mono (scalarByte_ok s k hk hi.counter hread hv) fun t ⟨htb, htz, htv, htk⟩ => ?_
    have kt := hi.keeps.trans htk
    have vt : scalarValue t = decodeLE ((bytesAt s₀.mem (s₀.gpr .rsi) 64).drop k) % L := by
      rw [htv, hi.value, hp, hi.keeps.2.1, suffix_step _ _ k hk]
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, htz, decide_true, Option.map_some, Bool.not_true],
        by simpa only [List.drop_zero] using vt, kt⟩
    · exact Or.inr ⟨by simp only [eval, htz, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega, ⟨by omega, by omega, htb, vt, kt⟩⟩
  · refine ⟨by decide, by decide, hb, ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
    rw [hz, List.drop_eq_nil_of_le (by rw [bytesAt_length])]
    rfl

end VG.Proof.Ed25519.X86_64
