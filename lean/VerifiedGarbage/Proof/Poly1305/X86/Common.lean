import VerifiedGarbage.Proof.Poly1305.X86.Reduce
import VerifiedGarbage.Proof.Poly1305.Spec

/-!
# Poly1305 on x86 (32-bit): the state in memory, as the specification sees it

Untrusted: everything here is checked by Lean. Little-endian numbers of
32-bit words in memory, the key and its clamped `r`, and the tag.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P clamp leNum leBytes bytesAt accumulate Repr)

/-! ## Numbers as words -/

theorem leNum_bytesAt_4 (m : Mem) (p : Addr) : leNum (bytesAt m p 4) = (m.readW p 32).toNat := by
  rw [Poly1305.leNum_bytesAt_read]; simp [Mem.readW]

theorem leNum_bytesAt_4add (m : Mem) (p : Addr) (n : Nat) :
    leNum (bytesAt m p (4 + n)) =
      (m.readW p 32).toNat + 2 ^ 32 * leNum (bytesAt m (p + BitVec.ofNat 64 4) n) := by
  rw [Poly1305.bytesAt_add, Poly1305.leNum_append, Poly1305.length_bytesAt, leNum_bytesAt_4]
  rfl

/-- The word at `p + 4 k`, as a number. -/
abbrev w32 (m : Mem) (p : Addr) (k : Nat) : Nat := (m.readW (p + BitVec.ofNat 64 (4 * k)) 32).toNat

theorem add_ofNat_add (p : Addr) (d e : Nat) :
    p + BitVec.ofNat 64 d + BitVec.ofNat 64 e = p + BitVec.ofNat 64 (d + e) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Four little-endian words. -/
theorem leNum_bytesAt_16 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = w32 m p 0 + 2 ^ 32 * w32 m p 1 + 2 ^ 64 * w32 m p 2 + 2 ^ 96 * w32 m p 3 := by
  rw [show 16 = 4 + (4 + (4 + (4 + 0))) from rfl, leNum_bytesAt_4add, leNum_bytesAt_4add,
    leNum_bytesAt_4add, leNum_bytesAt_4add]
  simp only [w32, add_ofNat_add, show bytesAt m _ 0 = [] from rfl, Spec.Poly1305.leNum, BitVec.add_zero,
    Nat.mul_zero, Nat.add_zero]
  ring

/-- Six little-endian words. -/
theorem leNum_bytesAt_24 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 24) = w32 m p 0 + 2 ^ 32 * w32 m p 1 + 2 ^ 64 * w32 m p 2 + 2 ^ 96 * w32 m p 3 +
      2 ^ 128 * w32 m p 4 + 2 ^ 160 * w32 m p 5 := by
  rw [show 24 = 4 + (4 + (4 + (4 + (4 + (4 + 0))))) from rfl, leNum_bytesAt_4add, leNum_bytesAt_4add,
    leNum_bytesAt_4add, leNum_bytesAt_4add, leNum_bytesAt_4add, leNum_bytesAt_4add]
  simp only [w32, add_ofNat_add, show bytesAt m _ 0 = [] from rfl, Spec.Poly1305.leNum, BitVec.add_zero,
    Nat.mul_zero, Nat.add_zero]
  ring

/-- A word of the state as the specification addresses it. -/
theorem w32_eq {m : Mem} {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {k : Nat} (hk : k < 32) :
    w32 m (st.setWidth 64) k = wv m st (4 * k) := by
  rw [wv, wd, addr_eq (by omega)]

theorem w32_off {m : Mem} {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {d k : Nat}
    (hk : d + 4 * k + 4 ≤ 128) : w32 m (st.setWidth 64 + BitVec.ofNat 64 d) k = wv m st (d + 4 * k) := by
  simp only [w32, wv, wd]
  rw [addr_eq (by omega), add_ofNat_add]

/-- The accumulator in the state's words. -/
theorem leNum_acc {m : Mem} {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {f : Nat → Nat}
    (hw : Words m st f) :
    leNum (bytesAt m (st.setWidth 64) 24) = hw5 f + 2 ^ 160 * f 5 := by
  rw [leNum_bytesAt_24, w32_eq hfit (by omega), w32_eq hfit (by omega), w32_eq hfit (by omega),
    w32_eq hfit (by omega), w32_eq hfit (by omega), w32_eq hfit (by omega), hw 0 (by omega),
    hw 1 (by omega), hw 2 (by omega), hw 3 (by omega), hw 4 (by omega), hw 5 (by omega)]
  rfl

/-- The accumulator of a state that represents a message, below `p`, as words. -/
theorem acc_words {m : Mem} {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {f : Nat → Nat}
    (hw : Words m st f) (hlt : leNum (bytesAt m (st.setWidth 64) 24) < P) :
    f 5 = 0 ∧ f 4 ≤ 3 ∧ leNum (bytesAt m (st.setWidth 64) 24) = hw5 f := by
  rw [leNum_acc hfit hw] at hlt ⊢
  have h0 := hw.lt (k := 0) (by omega); have h1 := hw.lt (k := 1) (by omega)
  have h2 := hw.lt (k := 2) (by omega); have h3 := hw.lt (k := 3) (by omega)
  simp only [hw5, val5, P] at hlt ⊢
  omega

/-! ## Bytes as words -/

/-- Bytes of memory are the same where the words are. -/
theorem bytesAt_congr_words2 {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ k < n, m'.readW (p + BitVec.ofNat 64 (4 * k)) 32 = m.readW (q + BitVec.ofNat 64 (4 * k)) 32) :
    bytesAt m' p (4 * n) = bytesAt m q (4 * n) := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have e : ∀ x : Addr, x + BitVec.ofNat 64 i = (x + BitVec.ofNat 64 (4 * (i / 4))) + BitVec.ofNat 64 (i % 4) :=
    fun x => by rw [add_ofNat_add]; congr 2; omega
  rw [e p, e q, Mem.readW_byte m' _ (Nat.mod_lt _ (by omega)), Mem.readW_byte m _ (Nat.mod_lt _ (by omega)),
    h _ (by omega)]

theorem bytesAt_congr_words {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ k < n, m'.readW (p + BitVec.ofNat 64 (4 * k)) 32 = m.readW (p + BitVec.ofNat 64 (4 * k)) 32) :
    bytesAt m' p (4 * n) = bytesAt m p (4 * n) := bytesAt_congr_words2 h

/-! ## The key -/

theorem land_split32 {a b c d : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (a + 2 ^ 32 * b) &&& (c + 2 ^ 32 * d) = (a &&& c) + 2 ^ 32 * (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hac : (a &&& c) < 2 ^ 32 := lt_of_le_of_lt Nat.and_le_left ha
  rw [Nat.testBit_and]
  rw [Nat.add_comm a, Nat.add_comm c, Nat.add_comm (a &&& c)]
  rw [Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ hac]
  split <;> simp [Nat.testBit_and]

/-- The clamped `r` of a key of four little-endian words. -/
theorem clamp_words4 {k0 k1 k2 k3 : Nat} (h0 : k0 < 2 ^ 32) (h1 : k1 < 2 ^ 32) (h2 : k2 < 2 ^ 32) :
    clamp (k0 + 2 ^ 32 * k1 + 2 ^ 64 * k2 + 2 ^ 96 * k3) =
      (k0 &&& 0x0fffffff) + 2 ^ 32 * (k1 &&& 0x0ffffffc) + 2 ^ 64 * (k2 &&& 0x0ffffffc) +
        2 ^ 96 * (k3 &&& 0x0ffffffc) := by
  have e : ∀ x y z w : Nat, x + 2 ^ 32 * y + 2 ^ 64 * z + 2 ^ 96 * w =
      x + 2 ^ 32 * (y + 2 ^ 32 * (z + 2 ^ 32 * w)) := fun x y z w => by ring
  rw [clamp, e, show (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat) =
    0x0fffffff + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * 0x0ffffffc)) by norm_num,
    land_split32 h0 (by norm_num), land_split32 h1 (by norm_num), land_split32 h2 (by norm_num), e]

theorem mask0_lt (k : Nat) : k &&& 0x0fffffff < 2 ^ 28 :=
  lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem mask1_lt (k : Nat) : k &&& 0x0ffffffc < 2 ^ 28 :=
  lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem mask1_mod (k : Nat) : (k &&& 0x0ffffffc) % 4 = 0 := by
  rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    show (0x0ffffffc : Nat) &&& 2 ^ 2 - 1 = 0 by decide, Nat.and_zero]

/-! ## The tag -/

theorem bytesAt_leBytes_4 (m : Mem) (p : Addr) : bytesAt m p 4 = leBytes 4 (m.readW p 32).toNat := by
  rw [Poly1305.bytesAt_leBytes]; simp [Mem.readW]

/-- Four little-endian words in memory are the 16 bytes of `x`, if they are its
low 128 bits. -/
theorem bytesAt_leBytes_16w (m : Mem) (p : Addr) (x : Nat) (h : ∀ k < 4, w32 m p k = x / 2 ^ (32 * k) % 2 ^ 32) :
    bytesAt m p 16 = leBytes 16 x := by
  have e : ∀ k < 4, bytesAt m (p + BitVec.ofNat 64 (4 * k)) 4 = leBytes 4 (x / 2 ^ (32 * k)) := by
    intro k hk
    rw [bytesAt_leBytes_4, show (m.readW (p + BitVec.ofNat 64 (4 * k)) 32).toNat = w32 m p k from rfl,
      h k hk, show (2 : Nat) ^ 32 = 256 ^ 4 by norm_num, Poly1305.leBytes_mod]
  rw [show 16 = 4 + (4 + (4 + 4)) from rfl, Poly1305.bytesAt_add, Poly1305.bytesAt_add,
    Poly1305.bytesAt_add, Poly1305.leBytes_add, Poly1305.leBytes_add, Poly1305.leBytes_add,
    add_ofNat_add, add_ofNat_add]
  have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
  have e3 := e 3 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.pow_zero, Nat.div_one] at e0
  rw [e0, e1, e2, e3, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.pow_add]
  norm_num

end VG.Proof.Poly1305.X86
