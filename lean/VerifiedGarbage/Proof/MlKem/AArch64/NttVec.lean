import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.Ntt
import VerifiedGarbage.Proof.MlKem.AArch64.Common

/-!
# ML-KEM on AArch64: polynomials in vectors

Untrusted: everything here is checked by Lean. Four coefficients of a
polynomial loaded into a vector (`lanes_load`) and two vectors stored into it
(`polyIs_write16x2`). The butterflies of a block of the NTT and its inverse
some at a time are in `Proof/MlKem/Ntt.lean` (`nttBlockN_add`,
`nttBlockN_get'`).
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64
open VG.Spec.MlKem

theorem coeffAddr_off (p : Addr) (j k : Nat) :
    coeffAddr p j + BitVec.ofNat 64 (4 * k) = coeffAddr p (j + k) := by
  rw [coeffAddr, coeffAddr, ptr_add, Nat.mul_add]

/-- The 16 bytes at coefficient `j` of `P`, as lanes. -/
theorem lanes_load {m : Mem} {p : Addr} {P : Poly} (h : PolyIs m p P) {j : Nat} (hj : j + 4 ≤ 256) :
    Lanes (m.read (coeffAddr p j) 16) fun e => (P[j + e]!).val := fun e he => by
  rw [read16, vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
    rw [coeffAddr_off, ← coeffAt_eq, polyIs_toNat h (show _ < n by rw [n_eq]; omega)]

/-- Coefficient `i` after storing the vector `x` at coefficient `j`. -/
theorem coeffAt_write16 (m : Mem) (p : Addr) {j : Nat} (hj : j + 4 ≤ 256) (x : BitVec 128) {i : Nat}
    (hi : i < 256) :
    coeffAt (m.write (coeffAddr p j) 16 x) p i =
      if j ≤ i ∧ i < j + 4 then vword x (i - j) else coeffAt m p i := by
  rw [← ofVWords_vword x, write16, show coeffAddr p j + BitVec.ofNat 64 4 = coeffAddr p (j + 1) from
      coeffAddr_off p j 1, show coeffAddr p j + BitVec.ofNat 64 8 = coeffAddr p (j + 2) from
      coeffAddr_off p j 2, show coeffAddr p j + BitVec.ofNat 64 12 = coeffAddr p (j + 3) from
      coeffAddr_off p j 3]
  have hn : ∀ k, k < 4 → j + k < n := fun k hk => by rw [n_eq]; omega
  rw [coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) (hn 3 (by decide)),
    coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) (hn 2 (by decide)),
    coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) (hn 1 (by decide)),
    coeffAt_writeW _ _ (show i < n by rw [n_eq]; omega) (show j < n by rw [n_eq]; omega)]
  rcases (by omega : i < j ∨ i = j ∨ i = j + 1 ∨ i = j + 2 ∨ i = j + 3 ∨ j + 4 ≤ i) with
    h | rfl | rfl | rfl | rfl | h <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right, ↓reduceIte, Nat.sub_self,
      Nat.add_sub_cancel_left, ofVWords_vword]

/-- Two vectors stored into a polynomial, with the lanes `a` and `b`. -/
theorem polyIs_write16x2 {m : Mem} {p : Addr} {P R : Poly} (hP : PolyIs m p P) {j j' : Nat}
    (hj : j + 4 ≤ 256) (hj' : j' + 4 ≤ 256) (hsep : j + 4 ≤ j' ∨ j' + 4 ≤ j) {x y : BitVec 128}
    {a b : Nat → Zq} (hx : Lanes x fun e => (a e).val) (hy : Lanes y fun e => (b e).val)
    (hR : ∀ i < 256, R[i]! = if j ≤ i ∧ i < j + 4 then a (i - j)
      else if j' ≤ i ∧ i < j' + 4 then b (i - j') else P[i]!) :
    PolyIs ((m.write (coeffAddr p j) 16 x).write (coeffAddr p j') 16 y) p R :=
  polyIs_of_toNat fun i hi => by
    rw [n_eq] at hi
    rw [coeffAt_write16 _ _ hj' _ hi, coeffAt_write16 _ _ hj _ hi, hR i hi]
    by_cases h1 : j' ≤ i ∧ i < j' + 4
    · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left h1, hy _ (by omega)]
    · rw [ite_eq_right h1]
      by_cases h2 : j ≤ i ∧ i < j + 4
      · rw [ite_eq_left h2, ite_eq_left h2, hx _ (by omega)]
      · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_right h1, polyIs_toNat hP (by rw [n_eq]; exact hi)]

theorem frame16 {m m' : Mem} {p : Addr} (hf : Frame [polyRegion p] m m') {j : Nat} (hj : j + 4 ≤ 256)
    (x : BitVec 128) : Frame [polyRegion p] m (m'.write (coeffAddr p j) 16 x) :=
  hf.write (n := 16) (List.mem_singleton_self _) x (contains_off (by omega) (by decide))

theorem coeffAddr_step (p : Addr) (a : Nat) :
    coeffAddr p a + BitVec.ofNat 64 16 = coeffAddr p (a + 4) := by
  rw [coeffAddr, coeffAddr, ptr_add, show 4 * a + 16 = 4 * (a + 4) by omega]

theorem CoeffsUpTo.write16 {m : Mem} {p : Addr} {t : Nat} {G old : Nat → BitVec 32}
    (h : CoeffsUpTo m p t G old) (ht : t + 4 ≤ 256) {x : BitVec 128}
    (hx : ∀ e < 4, vword x e = G (t + e)) : CoeffsUpTo (m.write (coeffAddr p t) 16 x) p (t + 4) G old :=
  fun i hi => by
    rw [coeffAt_write16 _ _ ht _ hi, h i hi]
    by_cases c : t ≤ i ∧ i < t + 4
    · rw [ite_eq_left c, ite_eq_left (by omega), hx _ (by omega), show t + (i - t) = i by omega]
    · rw [ite_eq_right c]
      by_cases c' : i < t
      · rw [ite_eq_left c', ite_eq_left (by omega)]
      · rw [ite_eq_right c', ite_eq_right (by omega)]

/-- The lanes of four coefficients, from their values. -/
theorem lanes_coeffs {m : Mem} {p : Addr} {j : Nat} {A : Nat → Nat}
    (h : ∀ e < 4, (coeffAt m p (j + e)).toNat = A e) : Lanes (m.read (coeffAddr p j) 16) A :=
  fun e he => by
    rw [read16, vword_ofVWords _ _ _ _ he]
    rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
      rw [coeffAddr_off, ← coeffAt_eq] <;> exact h _ (by decide)

end VG.Proof.MlKem.AArch64
