import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Call
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Streaming AES-CMAC on ARMv7: arithmetic and memory

Untrusted: everything here is checked by Lean. `count` in a register pair
(`toNat_append32`, `or_beq_zero`), the number of bytes held back as the
code computes it from the low word of `count` (`held_lo`), conditions, and
bytes written.
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm
open VG.Proof.Cmac.Stream (held held_pos held_zero)
open VG.Proof.MdStream.Arm (eval_eq eval_ne ofNat_beq_zero sub_ofNat cmp0)

/-! ## `count` in a register pair -/

theorem toNat_append32 (hi lo : BitVec 32) : (hi ++ lo : BitVec 64).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

/-- A count in a register pair is zero iff the OR of its words is. -/
theorem or_beq_zero {lo hi : BitVec 32} {x : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x)
    (hx : x < 2 ^ 64) : ((lo ||| hi) - 0 == 0) = decide (x = 0) := by
  have e := congrArg BitVec.toNat h
  rw [toNat_append32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at e
  rw [show (lo ||| hi) - 0 = lo ||| hi from BitVec.sub_zero _]
  by_cases hx0 : x = 0
  · have h1 : lo = 0 := BitVec.eq_of_toNat_eq (by show lo.toNat = 0; omega)
    have h2 : hi = 0 := BitVec.eq_of_toNat_eq (by show hi.toNat = 0; omega)
    simp [h1, h2, hx0]
  · rw [decide_eq_false hx0, beq_eq_false_iff_ne]
    intro h0
    obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h0
    rw [h1, h2] at e
    rw [BitVec.toNat_zero] at e
    omega

theorem count_eq (s : State) : (s.gpr .r3 ++ s.gpr .r2 : BitVec 64) = BitVec.ofNat 64 (countArm s).toNat :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]; rfl)

theorem and15 (x : BitVec 32) : (x &&& 15).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The number of bytes held back for a nonzero count, as `sub 1; and 15;
add 1` computes it from its low word. -/
theorem held_lo {lo hi : BitVec 32} {x : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x)
    (hx : x < 2 ^ 64) (h0 : x ≠ 0) : ((lo - 1) &&& 15) + 1 = BitVec.ofNat 32 (held x) := by
  have e := congrArg BitVec.toNat h
  rw [toNat_append32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at e
  rw [held_pos (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and15, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  have := lo.isLt
  have := hi.isLt
  omega

/-! ## Conditions -/

theorem ne_iff (s : State) {k : Nat} (h : s.z = (BitVec.ofNat 32 k - 0 == 0)) (hk : k < 2 ^ 32) :
    isa.eval .ne s = some (decide (k ≠ 0)) := by
  show VG.Arm.eval .ne s = _
  rw [eval_ne, h, cmp0 hk]
  simp

theorem eq_iff (s : State) {k : Nat} (h : s.z = (BitVec.ofNat 32 k - 0 == 0)) (hk : k < 2 ^ 32) :
    isa.eval .eq s = some (decide (k = 0)) := by
  show VG.Arm.eval .eq s = _
  rw [eval_eq, h, cmp0 hk]

/-- A pointer plus an offset that does not wrap. -/
theorem toNat_add_ofNat {p : BitVec 32} {k : Nat} (h : p.toNat + k < 2 ^ 32) :
    (p + BitVec.ofNat 32 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem toNat_ofNat64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem add_ofNat32 (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## Bytes written -/

section
open VG.WriteBytes

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} (h : xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 _
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, bytesAt_writeBytes_self _ _ (by omega)]
  congr 1
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact writeBytes_before m p xs (List.mem_range.mp hi) (by omega)

end

end VG.Proof.CmacAes.Stream.Arm
