import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.TCB.Arm.Isa

/-!
# ARMv7: the bytes of a word

Untrusted: everything here is checked by Lean. The bits of a word loaded
from memory (little-endian), and of `rev` of a word.
-/

namespace VG.Arm

theorem readW_bit (m : Mem) (a : Addr) {i t : Nat} (hi : i < 4) (ht : t < 8) :
    (m.readW a 32).getLsbD (8 * i + t) = (m (a + BitVec.ofNat 64 i)).getLsbD t := by
  rw [← Mem.extractLsb'_read m a (n := 4) hi, BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, ht, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_setWidth]
  simp [show 8 * i + t < 32 by omega]

theorem rev_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (rev v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold rev
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals first | omega | (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

theorem out_of_disj {r₁ r₂ : Region} (hd : r₁.Disjoint r₂) {x a : Addr} {n : Nat} (hx : r₁.Contains x 1)
    (ha : r₂.Contains a n) : ¬ (x - a).toNat < n := fun h => hd x hx (ha.byte h)

theorem st_byte (m : Mem) (a : Addr) (v : BitVec 32) {t : Nat} (ht : t < 4) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8 * t) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a ht, Mem.readW_writeW_self32]

theorem writeW32_other {m : Mem} {a x : Addr} (v : BitVec 32) (h : Region.Disjoint ⟨x, 1⟩ ⟨a, 4⟩) :
    m.writeW a v x = m x :=
  Mem.write_apply (out_of_disj h (Region.contains_self _ _) (Region.contains_self _ _))

theorem off_disjoint (B : Addr) {x lx y ly : Nat} (h : x + lx ≤ y ∨ y + ly ≤ x)
    (hx : x + lx < 2 ^ 64) (hy : y + ly < 2 ^ 64) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 x, lx⟩ ⟨B + BitVec.ofNat 64 y, ly⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rcases h with h | h <;> bv_omega

theorem off_sub (B : Addr) {x lx y ly : Nat} (h1 : y ≤ x) (h2 : x + lx ≤ y + ly) (hy : y + ly < 2 ^ 64) :
    Region.Sub ⟨B + BitVec.ofNat 64 x, lx⟩ ⟨B + BitVec.ofNat 64 y, ly⟩ := by
  intro a h
  simp only [Region.Contains] at h ⊢
  bv_omega

theorem rev_rev (x : BitVec 32) : rev (rev x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨k, j, hk, hj, rfl⟩ : ∃ k j, k < 4 ∧ j < 8 ∧ i = 8 * k + j :=
    ⟨i / 8, i % 8, by omega, by omega, by omega⟩
  rw [rev_bit _ hk hj, rev_bit _ (by omega) hj]
  congr 1
  omega

end VG.Arm
