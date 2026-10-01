import VerifiedGarbage.Proof.Sha3.X86_64.X4.Loop

/-!
# Keccak-f[1600] four times at once on x86-64: the states byte by byte

Untrusted: everything here is checked by Lean. Byte `q` of state `k` of the
four interleaved at `p` is at `ba p k q` (byte `q % 8` of lane `q / 8`); the
lanes hold the states exactly when these bytes are theirs
(`lanes4_of_bytes`, `byte_of_lanes4`).
-/

namespace VG.Proof.Sha3.X86_64.X4

open VG VG.X86_64
open VG.Proof.Sha3 (byteOf byteOf_eq getElem!_eq)

/-- Byte `q` of state `k` of the four at `p`. -/
abbrev ba (p : Addr) (k q : Nat) : Addr := p + BitVec.ofNat 64 (32 * (q / 8) + 8 * k + q % 8)

/-- Two lanes with the same bytes. -/
theorem lane_ext {v w : BitVec 64} (h : ∀ j < 8, v.extractLsb' (8 * j) 8 = w.extractLsb' (8 * j) 8) :
    v = w := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have := congrArg (·.getLsbD (b % 8)) (h (b / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show b % 8 < 8 by omega, decide_true, Bool.true_and] at this
  rwa [show 8 * (b / 8) + b % 8 = b by omega] at this

theorem la_byte (p : Addr) {i k j : Nat} (hj : j < 8) :
    la p i k + BitVec.ofNat 64 j = ba p k (8 * i + j) := by
  rw [la, BitVec.add_assoc, ← BitVec.ofNat_add, ba, show (8 * i + j) / 8 = i by omega,
    show (8 * i + j) % 8 = j by omega]

theorem lanes4_of_bytes {m : Mem} {p : Addr} {A : Nat → KState}
    (h : ∀ k < 4, ∀ q < 200, m (ba p k q) = byteOf (A k) q) : Lanes4 m p A := fun i hi k hk =>
  lane_ext fun j hj => by
    rw [byte_readW _ _ (by omega), la_byte _ hj, h k hk _ (by omega), byteOf_eq _ hi hj, getElem!_eq _ hi]

theorem byte_of_lanes4 {m : Mem} {p : Addr} {A : Nat → KState} (h : Lanes4 m p A) {k q : Nat} (hk : k < 4)
    (hq : q < 200) : m (ba p k q) = byteOf (A k) q := by
  rw [byteOf, ← h (q / 8) (by omega) k hk, byte_readW _ _ (by omega), la_byte _ (by omega),
    show 8 * (q / 8) + q % 8 = q by omega]

end VG.Proof.Sha3.X86_64.X4
