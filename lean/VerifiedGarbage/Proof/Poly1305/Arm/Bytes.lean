import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Poly1305.Arm.Setup
import Mathlib.Tactic.Ring.RingNF

/-!
# Poly1305 on 32-bit ARM: bytes and words in memory

Untrusted: everything here is checked by Lean. Byte strings in memory as
32-bit little-endian words (`bytesAt_eq_of_words`, `leNum_bytesAt_words`),
the clamped `r` of a stored key as limbs (`val_rlimb`), and regions of the
state.
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt)

/-! ## Words -/

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-- Two byte strings are equal if their words are. -/
theorem bytesAt_eq_of_words {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ j < n, m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = m'.readW (q + BitVec.ofNat 64 (4 * j)) 32) :
    bytesAt m p (4 * n) = bytesAt m' q (4 * n) := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  have e : ∀ a : Addr, a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (4 * (i / 4)) + BitVec.ofNat 64 (i % 4) :=
    fun a => by rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod]
  rw [e p, e q, Mem.readW_byte m _ (Nat.mod_lt _ (by omega)), Mem.readW_byte m' _ (Nat.mod_lt _ (by omega)),
    h _ (by omega)]

theorem leNum_bytesAt_4 (m : Mem) (p : Addr) : leNum (bytesAt m p 4) = (m.readW p 32).toNat := by
  rw [Poly1305.leNum_bytesAt_read]
  simp [Mem.readW]

/-- A byte string as little-endian words. -/
theorem leNum_bytesAt_words (m : Mem) (p : Addr) : ∀ n,
    leNum (bytesAt m p (4 * n)) = rsum (fun j => 2 ^ (32 * j) * (m.readW (p + BitVec.ofNat 64 (4 * j)) 32).toNat) n
  | 0 => by simp [bytesAt, rsum, Spec.Poly1305.leNum]
  | n + 1 => by
    rw [show 4 * (n + 1) = 4 * n + 4 by ring, Poly1305.bytesAt_add, Poly1305.leNum_append,
      Poly1305.length_bytesAt, leNum_bytesAt_4, leNum_bytesAt_words m p n, rsum,
      show (256 : Nat) ^ (4 * n) = 2 ^ (32 * n) by rw [Nat.pow_mul, Nat.pow_mul]]

theorem leNum_bytesAt_16 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = (m.readW (p + BitVec.ofNat 64 0) 32).toNat +
      2 ^ 32 * (m.readW (p + BitVec.ofNat 64 4) 32).toNat + 2 ^ 64 * (m.readW (p + BitVec.ofNat 64 8) 32).toNat +
      2 ^ 96 * (m.readW (p + BitVec.ofNat 64 12) 32).toNat := by
  rw [show 16 = 4 * 4 from rfl, leNum_bytesAt_words]
  simp only [rsum]
  ring

theorem leNum_bytesAt_24 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 24) = (m.readW (p + BitVec.ofNat 64 0) 32).toNat +
      2 ^ 32 * (m.readW (p + BitVec.ofNat 64 4) 32).toNat + 2 ^ 64 * (m.readW (p + BitVec.ofNat 64 8) 32).toNat +
      2 ^ 96 * (m.readW (p + BitVec.ofNat 64 12) 32).toNat +
      2 ^ 128 * (m.readW (p + BitVec.ofNat 64 16) 32).toNat +
      2 ^ 160 * (m.readW (p + BitVec.ofNat 64 20) 32).toNat := by
  rw [show 24 = 4 * 6 from rfl, leNum_bytesAt_words]
  simp only [rsum]
  ring

/-! ## The stored key -/

theorem off_add (B : Addr) (a d : Nat) :
    B + BitVec.ofNat 64 a + BitVec.ofNat 64 d = B + BitVec.ofNat 64 (a + d) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem take_bytesAt (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) :
    (bytesAt m p n).take k = bytesAt m p k := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem drop_bytesAt (m : Mem) (p : Addr) (k n : Nat) :
    (bytesAt m p (k + n)).drop k = bytesAt m (p + BitVec.ofNat 64 k) n := by
  rw [Poly1305.bytesAt_add, List.drop_left' (Poly1305.length_bytesAt _ _ _)]

/-- The number of the key's first 16 bytes, as four words at `[24, 40)` of the state. -/
theorem leNum_r (m : Mem) (B : Addr) :
    leNum (bytesAt m (B + 24) 16) = (m.readW (B + BitVec.ofNat 64 24) 32).toNat +
      2 ^ 32 * (m.readW (B + BitVec.ofNat 64 28) 32).toNat +
      2 ^ 64 * (m.readW (B + BitVec.ofNat 64 32) 32).toNat +
      2 ^ 96 * (m.readW (B + BitVec.ofNat 64 36) 32).toNat := by
  rw [leNum_bytesAt_16, show (24 : Addr) = BitVec.ofNat 64 24 from rfl, off_add, off_add, off_add, off_add]

theorem val_rlimb (m : Mem) (B : Addr) :
    val (rlimb m B) = clamp (leNum (bytesAt m (B + 24) 16)) := by
  have hc : ∀ i, (cw m B i).toNat < 2 ^ 32 := fun i => (cw m B i).isLt
  rw [rlimb, val_mlimb (hc 0) (hc 1) (hc 2) (hc 3), leNum_r,
    clamp_words (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)]
  simp only [cw, BitVec.toNat_and, Nat.mul_zero, Nat.add_zero, show (1 : Nat) ≠ 0 by decide,
    show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide, ite_true, ite_false]
  rfl

theorem rlimb_frame {m m' : Mem} {B : Addr} (h : ∀ i < 4,
    m'.readW (B + BitVec.ofNat 64 (24 + 4 * i)) 32 = m.readW (B + BitVec.ofNat 64 (24 + 4 * i)) 32) :
    rlimb m' B = rlimb m B := by
  simp only [rlimb, cw, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

/-! ## Regions of the state -/

theorem sub_base (p : Addr) {a len len' : Nat} (h : a + len ≤ len') (h' : len' < 2 ^ 64) :
    Region.Sub ⟨p + BitVec.ofNat 64 a, len⟩ ⟨p, len'⟩ := by
  intro x hx
  simp only [Region.Contains] at *
  rw [show x - p = (x - (p + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by bv_omega, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem contains_base (p : Addr) {d n len : Nat} (h : d + n ≤ len) (h' : len < 2 ^ 32) :
    (⟨p, len⟩ : Region).Contains (p + BitVec.ofNat 64 d) n :=
  contains_off h (by omega)

/-- A region inside `[B + a, B + a + la)` is disjoint from one outside it. -/
theorem disjoint_of_sub {r₁ r₂ r₁' r₂' : Region} (h : r₁'.Disjoint r₂') (h₁ : Region.Sub r₁ r₁')
    (h₂ : Region.Sub r₂ r₂') : r₁.Disjoint r₂ :=
  (h.sub_left h₁).sub_right h₂

end VG.Proof.Poly1305.Arm
