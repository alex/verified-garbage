import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch

/-! Untrusted: the invariant of the descent through the checkpoint table. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem batch_counter_nonzero : ∀ n < 32,
    (BitVec.ofNat 64 n != 0) = decide (n ≠ 0) := by decide

structure PointMulInv (s₀ : State) (base : Addr) (count scalar : Nat) (p : Spec.Ed25519.Point)
    (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ count
  scratch : Scr s base
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 n
  d : env s.mem base 16 = Spec.Ed25519.d
  value : point (env s.mem base) 0 1 2 3 = after scalar p (16 * n)
  bits : ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)
  table : ∀ i < count, tablePoint s.mem base (1280 + 128 * i) = powerPoint p (16 * i)
  keep : PowersKeep base 56 7368 s₀ s

end VG.Proof.Ed25519.AArch64
