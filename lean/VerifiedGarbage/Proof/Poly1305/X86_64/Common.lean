import VerifiedGarbage.Proof.Poly1305.X86_64.Reduce
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Poly1305 on x86-64: the state in memory, and loading the key

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The address `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofInt 64 (d : Int)

theorem contains_off {base : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (off base d) n := by
  simp only [Region.Contains, off, ofInt_natCast]
  rw [show base + BitVec.ofNat 64 d - base = BitVec.ofNat 64 d by bv_omega, toNat_ofNat_lt hd]
  exact h

theorem sep_off (p : Addr) {d e n k : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32) (hn : n ≤ 16)
    (hk : k ≤ 16) (h : d + n ≤ e ∨ e + k ≤ d) : Mem.Sep (off p d) n (off p e) k := by
  intro x hx hy
  simp only [off, ofInt_natCast] at hx hy
  bv_omega

theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 :=
  Mem.readW_writeW_sep (sep_off p hd he (by omega) (by omega) h) (by decide)

/-! ## The regions of the state -/

section
variable (st : Addr)
/-- The accumulator. -/
abbrev hR : Region := ⟨st, 24⟩
/-- The key. -/
abbrev kR : Region := ⟨off st 24, 32⟩
/-- The working space: the buffer and the saved registers. -/
abbrev wR : Region := ⟨off st 56, 72⟩
/-- The buffer. -/
abbrev bfR : Region := ⟨off st 56, 16⟩
/-- Where the callee-saved registers are saved. -/
abbrev svR : Region := ⟨off st 72, 48⟩
/-- The whole state. -/
abbrev sR : Region := ⟨st, 128⟩
end

theorem sub_sR (st : Addr) {d n : Nat} (h : d + n ≤ 128) : Region.Sub ⟨off st d, n⟩ (sR st) := by
  intro a ha
  simp only [Region.Contains, off, ofInt_natCast] at *
  bv_omega

theorem kR_disjoint (st : Addr) : ∀ r ∈ [hR st, wR st], (kR st).Disjoint r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) <;> intro a h₁ h₂ <;>
    simp only [Region.Contains, off, ofInt_natCast] at h₁ h₂ <;> bv_omega

/-- The key is unchanged by writes to the accumulator and the working space. -/
theorem key_frame {st : Addr} {m m' : Mem} (hf : Frame [hR st, wR st] m m') :
    bytesAt m' (off st 24) 32 = bytesAt m (off st 24) 32 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := kR st) (kR_disjoint st) (by simp) (List.mem_range.mp hi)

theorem hR_contains (st : Addr) {d : Nat} (h : d + 8 ≤ 24) : (hR st).Contains (off st d) 8 := by
  have := contains_off (base := st) (len := 24) h (by omega); simpa using this

theorem wR_contains (st : Addr) {d n : Nat} (h₁ : 56 ≤ d) (h₂ : d + n ≤ 128) :
    (wR st).Contains (off st d) n := by
  simp only [Region.Contains, off, ofInt_natCast]
  rw [show st + BitVec.ofNat 64 d - (st + BitVec.ofNat 64 56) = BitVec.ofNat 64 (d - 56) by bv_omega,
    toNat_ofNat_lt (by omega)]
  omega

theorem svR_contains (st : Addr) {d n : Nat} (h₁ : 72 ≤ d) (h₂ : d + n ≤ 120) :
    (svR st).Contains (off st d) n := by
  simp only [Region.Contains, off, ofInt_natCast]
  rw [show st + BitVec.ofNat 64 d - (st + BitVec.ofNat 64 72) = BitVec.ofNat 64 (d - 72) by bv_omega,
    toNat_ofNat_lt (by omega)]
  omega

theorem svR_sub_wR (st : Addr) : Region.Sub (svR st) (wR st) := by
  intro a ha
  simp only [Region.Contains, off, ofInt_natCast] at *
  bv_omega

/-! ## The accumulator and the key as numbers -/

theorem off_eq (p : Addr) (d : Nat) : off p d = p + BitVec.ofNat 64 d := by
  simp only [off, ofInt_natCast]

/-- The accumulator stored in the state. -/
theorem leNum_acc (m : Mem) (st : Addr) :
    leNum (bytesAt m st 24) = (m.readW (off st 0) 64).toNat + 2 ^ 64 * (m.readW (off st 8) 64).toNat +
      2 ^ 128 * (m.readW (off st 16) 64).toNat := by
  rw [leNum_bytesAt_24, off_eq, off_eq, off_eq, BitVec.add_zero]
  rfl

/-- The key stored in the state is the 32 bytes at `off st 24`. -/
theorem key_take (m : Mem) (st : Addr) :
    (bytesAt m (off st 24) 32).take 16 = bytesAt m (off st 24) 16 := by
  rw [show 32 = 16 + 16 from rfl, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]

theorem key_drop (m : Mem) (st : Addr) :
    ((bytesAt m (off st 24) 32).drop 16).take 16 = bytesAt m (off st 40) 16 := by
  rw [show 32 = 16 + 16 from rfl, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
    List.take_of_length_le (by rw [length_bytesAt])]
  congr 1
  simp only [off, ofInt_natCast]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem leNum_key (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = (m.readW (off p 0) 64).toNat + 2 ^ 64 * (m.readW (off p 8) 64).toNat := by
  rw [leNum_bytesAt_16, off_eq, off_eq, BitVec.add_zero]
  rfl

theorem off_24 (p : Addr) : off p 24 = p + 24 := by rw [off_eq]; rfl

theorem off_off (p : Addr) (d e : Nat) : off (off p d) e = off p (d + e) := by
  simp only [off, ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The clamped `r` as the code computes it. -/
abbrev M0 : BitVec 64 := 0x0ffffffc0fffffff
abbrev M1 : BitVec 64 := 0x0ffffffc0ffffffc

theorem clamp_key (m : Mem) (st : Addr) :
    clamp (leNum ((bytesAt m (off st 24) 32).take 16)) =
      (m.readW (off st 24) 64 &&& M0).toNat + 2 ^ 64 * (m.readW (off st 32) 64 &&& M1).toNat := by
  rw [key_take, leNum_key, off_off, off_off, clamp_words]

theorem r0_lt (k : BitVec 64) : (k &&& M0).toNat < 2 ^ 60 := by
  rw [BitVec.toNat_and]
  exact lt_of_le_of_lt Nat.and_le_right (by decide)

theorem r1_mod (k : BitVec 64) : (k &&& M1).toNat % 4 = 0 := by
  rw [BitVec.toNat_and, show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_assoc, show M1.toNat &&& 2 ^ 2 - 1 = 0 by decide, Nat.and_zero]

theorem r1_lt (k : BitVec 64) : (k &&& M1).toNat < 2 ^ 60 := by
  rw [BitVec.toNat_and]
  exact lt_of_le_of_lt Nat.and_le_right (by decide)

end VG.Proof.Poly1305.X86_64
