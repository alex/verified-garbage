import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch

/-! Untrusted: complete descent through the checkpoint table. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

structure PointMulInv (s₀ : State) (base : Addr) (count scalar : Nat) (p : Spec.Ed25519.Point)
    (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ count
  scratch : Scratch s base
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 n
  d : env s.mem base 16 = Spec.Ed25519.d
  value : point (env s.mem base) 0 1 2 3 = after scalar p (16 * n)
  bits : ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)
  table : ∀ i < count, tablePoint s.mem base (1280 + 128 * i) = powerPoint p (16 * i)
  keep : PowersKeep base 56 7368 s₀ s

theorem pointMulLoop_ok {s₀ : State} {base : Addr} (hs : Scratch s₀ base)
    (count scalar : Nat) (p : Spec.Ed25519.Point) (hn0 : 0 < count) (hn : count ≤ 32)
    (hc : s₀.mem.readW (off base 56) 64 = BitVec.ofNat 64 count)
    (hd : env s₀.mem base 16 = Spec.Ed25519.d)
    (hp : point (env s₀.mem base) 0 1 2 3 = after scalar p (16 * count))
    (hb : ∀ i < 16 * count, s₀.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2))
    (ht : ∀ i < count, tablePoint s₀.mem base (1280 + 128 * i) = powerPoint p (16 * i)) :
    WP isa (.loop pointMulBatch .ne) s₀ fun t =>
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointMul scalar p ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ PowersKeep base 56 7368 s₀ t := by
  apply WP.loop (PointMulInv s₀ base count scalar p) (n := count)
  · intro n s h
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hj : j < count := by have := h.bound; omega
    refine WP.mono (pointMulBatch_ok h.scratch j count scalar p hj hn h.counter h.d h.value h.bits h.table)
      fun t ⟨tc, tz, tv, td, tb, tt, tk⟩ => ?_
    by_cases hj0 : j = 0
    · subst hj0
      rw [Nat.mul_zero, after_zero] at tv
      exact Or.inl ⟨by simp only [eval, tz, decide_true, Option.map_some, Bool.not_true], tv, td, h.keep.trans tk⟩
    · exact Or.inr ⟨by simp only [eval, tz, decide_eq_false hj0, Option.map_some, Bool.not_false],
        j, by omega, ⟨by omega, by omega, tk.scratch h.scratch, tc, td, tv, tb, tt, h.keep.trans tk⟩⟩
  · exact ⟨hn0, Nat.le_refl _, hs, hc, hd, hp, hb, ht, PowersKeep.refl _ _ _ _⟩

end VG.Proof.Ed25519.X86_64
