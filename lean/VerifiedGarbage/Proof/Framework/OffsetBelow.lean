import VerifiedGarbage.Proof.Framework.Offset

/-!
# Byte ranges below a stack pointer

Untrusted: everything here is checked by Lean. As `Offset.lean`, for the
ranges `[E - d, E - d + n)` below an address `E` (a stack pointer, below which
calls push their return addresses): proven once for any offsets, so that a
proof about a particular range needs `omega` on the offsets rather than
`bv_omega` on the addresses.
-/

namespace VG.Offset

/-- `[E - m, E)` and `[E, E + l)` do not overlap. -/
theorem below_disjoint (E : Addr) {m l : Nat} (h : m + l ≤ 2 ^ 64) :
    Region.Disjoint ⟨E - BitVec.ofNat 64 m, m⟩ ⟨E, l⟩ := by
  have := disjoint_below_above E (m := m) (a := 0) (l := l) (by omega)
  rwa [BitVec.add_zero] at this

/-- `E - a - b` is `E - (a + b)`. -/
theorem sub_sub_ofNat (E : Addr) (a b : Nat) :
    E - BitVec.ofNat 64 a - BitVec.ofNat 64 b = E - BitVec.ofNat 64 (a + b) := by
  rw [← sub_add_eq, BitVec.ofNat_add]

end VG.Offset
