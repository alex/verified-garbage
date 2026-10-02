import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common

/-!
# PBKDF2 on the 32-bit targets, the whole derivation: what does not depend on the target

The output is the blocks `T₁ ‖ T₂ ‖ …` (`G`), of which `nb` are needed; after
`k` of them, the first `done k` bytes of the output are written. `INT (i)` is
the bytes of a byte-reversed word in memory (`bytes_rev_int`), and two
disjoint regions that do not wrap around fit in the address space together
(`len_add_le`). SHA-256's streaming state depends only on its bytes
(`sha256_repr`).
-/

namespace VG.Proof.Pbkdf2.Whole

open Spec.Sha256 (bytesAt)

/-! ## The blocks of the output -/

section
variable (prf : List Byte → List Byte) (salt : List Byte) (c D ol : Nat)

/-- `T_i`. -/
abbrev Tb (i : Nat) : List Byte := Spec.Pbkdf2.F prf salt c i

/-- `T₁ ‖ … ‖ T_k`. -/
def G (k : Nat) : List Byte := (List.range k).flatMap fun j => Tb prf salt c (j + 1)

theorem G_succ (k : Nat) : G prf salt c (k + 1) = G prf salt c k ++ Tb prf salt c (k + 1) := by
  simp only [G, List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem G_zero : G prf salt c 0 = [] := rfl

/-- The number of blocks of the output. -/
abbrev nb : Nat := (ol + D - 1) / D

/-- The bytes of the output after `k` blocks. -/
abbrev done (k : Nat) : Nat := min (k * D) ol

variable {D ol}

theorem lt_nb (hD : 0 < D) {k : Nat} : k < nb D ol ↔ k * D < ol := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hD, Nat.succ_mul]; omega

theorem ol_le (hD : 0 < D) : ol ≤ nb D ol * D := by
  have h1 : nb D ol * D + (ol + D - 1) % D = ol + D - 1 := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have h2 := Nat.mod_lt (ol + D - 1) hD
  omega

theorem nb_lt (hD : 0 < D) (h : ol ≤ (2 ^ 32 - 1) * D) : nb D ol < 2 ^ 32 := by
  rw [Nat.div_lt_iff_lt_mul hD]; omega

theorem nb_zero (hD : 0 < D) : nb D ol = 0 ↔ ol = 0 := by
  have := lt_nb (D := D) (ol := ol) hD (k := 0); simp only [Nat.zero_mul] at this; omega

theorem done_nb (hD : 0 < D) : done D ol (nb D ol) = ol := by
  have := ol_le (D := D) (ol := ol) hD; show min _ _ = _; omega

end

/-- PBKDF2's result, from the blocks of the output. -/
theorem pbkdf2_eq (prf : List Byte → List Byte) (salt : List Byte) {c D ol : Nat}
    (hol : ol ≤ (2 ^ 32 - 1) * D) {out : List Byte}
    (h : out = (G prf salt c (nb D ol)).take ol) :
    Spec.Pbkdf2.pbkdf2 prf D salt c ol = some out := by
  simp only [Spec.Pbkdf2.pbkdf2, show ¬ ((2 ^ 32 - 1) * D < ol) by omega, ↓reduceIte, h]
  rfl

/-! ## Memory -/

/-- Two disjoint regions below `N` fit below `N` together. -/
theorem len_add_le {r₁ r₂ : Region} {N : Nat} (hd : r₁.Disjoint r₂)
    (h₁ : r₁.base.toNat + r₁.len ≤ N) (h₂ : r₂.base.toNat + r₂.len ≤ N) : r₁.len + r₂.len ≤ N := by
  by_contra hc
  rcases Nat.le_total r₁.base.toNat r₂.base.toNat with hb | hb
  · refine hd r₂.base ?_ ?_ <;> simp only [Region.Contains]
    · rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hb)]; omega
    · simp only [BitVec.sub_self, BitVec.toNat_zero]; omega
  · refine hd r₁.base ?_ ?_ <;> simp only [Region.Contains]
    · simp only [BitVec.sub_self, BitVec.toNat_zero]; omega
    · rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hb)]; omega

/-- The bytes of `i`, big-endian: `INT (i)`. -/
theorem rev_int (i : Nat) :
    (List.range 4).map (fun j => (byteRev32 (BitVec.ofNat 32 i)).extractLsb' (8 * j) 8) = Spec.Pbkdf2.int i := by
  rw [byteRev32_extract]
  simp only [Spec.Pbkdf2.int, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] <;> omega

/-- The four bytes at `p` of memory whose word there is the byte reversal of
`i`: `INT (i)`. -/
theorem bytes_rev_int {m : Mem} {p : Addr} {i : Nat} (h : m.readW p 32 = byteRev32 (BitVec.ofNat 32 i)) :
    bytesAt m p 4 = Spec.Pbkdf2.int i := by
  rw [← rev_int, ← h]
  simp only [bytesAt]
  exact List.map_congr_left fun j hj => Mem.readW_byte m p (List.mem_range.mp hj)

theorem byteRev32_byteRev32 (x : BitVec 32) : byteRev32 (byteRev32 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [byteRev32]
  rw [getLsbD_cat4]
  simp only [BitVec.getLsbD_extractLsb']
  by_cases h1 : i < 8
  · simp only [h1, ite_true, decide_true, Bool.true_and]
    rw [getLsbD_cat4]
    simp only [show ¬ (24 + i < 8) by omega, show ¬ (24 + i < 16) by omega, show ¬ (24 + i < 24) by omega,
      ite_false, BitVec.getLsbD_extractLsb', show 24 + i - 24 = i by omega, h1, decide_true, Bool.true_and,
      Nat.zero_add]
  by_cases h2 : i < 16
  · simp only [h1, h2, ite_true, ite_false, decide_true, Bool.true_and, show i - 8 < 8 by omega]
    rw [getLsbD_cat4]
    simp only [show ¬ (16 + (i - 8) < 8) by omega, show ¬ (16 + (i - 8) < 16) by omega,
      show (16 + (i - 8) < 24) by omega, ite_false, ite_true, BitVec.getLsbD_extractLsb',
      show 16 + (i - 8) - 16 < 8 by omega, decide_true, Bool.true_and, show 8 + (16 + (i - 8) - 16) = i by omega]
  by_cases h3 : i < 24
  · simp only [h1, h2, h3, ite_true, ite_false, decide_true, Bool.true_and, show i - 16 < 8 by omega]
    rw [getLsbD_cat4]
    simp only [show ¬ (8 + (i - 16) < 8) by omega, show (8 + (i - 16) < 16) by omega, ite_false, ite_true,
      BitVec.getLsbD_extractLsb', show 8 + (i - 16) - 8 < 8 by omega, decide_true, Bool.true_and,
      show 16 + (8 + (i - 16) - 8) = i by omega]
  · simp only [h1, h2, h3, ite_false, decide_true, Bool.true_and, show i - 24 < 8 by omega]
    rw [getLsbD_cat4]
    simp only [show (0 + (i - 24) < 8) by omega, ite_true, BitVec.getLsbD_extractLsb', decide_true,
      Bool.true_and, show 24 + (0 + (i - 24)) = i by omega]

/-! ## SHA-256's streaming state -/

/-- SHA-256's streaming state depends only on its 96 bytes. -/
theorem sha256_repr (m m' : Mem) (p q : Addr) (msg : List Byte)
    (h : ∀ i < 96, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha256.Repr m p msg) : Spec.Sha256.Repr m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc h (by omega)
  · rw [← hr.2]
    exact Hmac.Generic.Common.bytesAt_reloc h (o := 32) (k := msg.length % 64) (by omega)

end VG.Proof.Pbkdf2.Whole
