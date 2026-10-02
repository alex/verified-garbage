import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Bfly
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (n Poly Zq PolyIs coeffAt)

theorem vword_read16 (m : Mem) (a : Addr) {e : Nat} (he : e < 4) :
    vword (m.read a 16) e = m.readW (a + BitVec.ofNat 64 (4*e)) 32 := by
  rw [VG.Proof.MlKem.AArch64.read16, vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem coeffs_load {m : Mem} {p : Addr} {F : Poly} (h : PolyIs m p F) {j : Nat}
    (hj : j+4 ≤ 256) : Coeffs (m.read (coeffAddr p j) 16) (fun e => F[j+e]!) := fun e he => by
  rw [vword_read16 _ _ he, coeffAddr_add, ← coeffAt_eq]
  exact polyIs_toNat h (by rw [n_eq]; omega)

theorem readW_write16 (m : Mem) (a : Addr) (v : BitVec 128) {j : Nat} (hj : j < 4) :
    (m.write a 16 v).readW (a + BitVec.ofNat 64 (4*j)) 32 = vword v j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vword, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth,
    hi, decide_true, Bool.true_and]
  rw [VG.Proof.MlKem.AArch64.getLsbD_read _ _ _ _ (by omega)]
  simp only [Mem.write]
  rw [show a + BitVec.ofNat 64 (4*j) + BitVec.ofNat 64 (i/8) - a = BitVec.ofNat 64 (4*j+i/8) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left]]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [show 4*j+i/8 < 16 by omega, ite_true, BitVec.getLsbD_extractLsb']
  rw [decide_eq_true (by omega), Bool.true_and]
  exact congrArg _ (by omega)

theorem coeffAt_write16 (m : Mem) (p : Addr) {j : Nat} (hj : j+4 ≤ 256)
    (v : BitVec 128) {i : Nat} (hi : i < 256) :
    coeffAt (m.write (coeffAddr p j) 16 v) p i =
      if j ≤ i ∧ i < j+4 then vword v (i-j) else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq, show coeffAddr p i = coeffAddr p j + BitVec.ofNat 64 (4*(i-j)) by
      rw [coeffAddr_add, show j+(i-j) = i by omega]]
    exact readW_write16 _ _ _ (by omega)
  · have hw : m.write (coeffAddr p j) 16 v = m.writeW (coeffAddr p j) v := by
      simp only [Mem.writeW, BitVec.setWidth_eq]
    rw [hw]
    exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem polyIs_write2 {m : Mem} {p : Addr} {P R : Poly} (hP : PolyIs m p P)
    {j j' : Nat} (hj : j+4 ≤ 256) (hj' : j'+4 ≤ 256) (hsep : j+4 ≤ j' ∨ j'+4 ≤ j)
    {x y : BitVec 128} {a b : Nat → Zq} (hx : Coeffs x a) (hy : Coeffs y b)
    (hR : ∀ i < 256, R[i]! = if j ≤ i ∧ i < j+4 then a (i-j)
      else if j' ≤ i ∧ i < j'+4 then b (i-j') else P[i]!) :
    PolyIs ((m.write (coeffAddr p j) 16 x).write (coeffAddr p j') 16 y) p R :=
  polyIs_of_toNat fun i hi => by
    rw [n_eq] at hi
    rw [coeffAt_write16 _ _ hj' _ hi, coeffAt_write16 _ _ hj _ hi, hR i hi]
    by_cases h1 : j' ≤ i ∧ i < j'+4
    · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left h1]
      exact hy _ (by omega)
    · rw [ite_eq_right h1]
      by_cases h2 : j ≤ i ∧ i < j+4
      · rw [ite_eq_left h2, ite_eq_left h2]; exact hx _ (by omega)
      · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_right h1]
        exact polyIs_toNat hP (by rw [n_eq]; exact hi)

theorem vector_contains (p : Addr) {j : Nat} (hj : j+4 ≤ 256) :
    (pR p).Contains (coeffAddr p j) 16 := Offset.contains_base p (by omega) (by omega)

theorem frame_write2 {m m' : Mem} {p : Addr} (hf : Frame [pR p] m m') {j j' : Nat}
    (hj : j+4 ≤ 256) (hj' : j'+4 ≤ 256) (x y : BitVec 128) :
    Frame [pR p] m ((m'.write (coeffAddr p j) 16 x).write (coeffAddr p j') 16 y) :=
  (hf.write (List.mem_singleton_self _) x (vector_contains p hj)).write
    (List.mem_singleton_self _) y (vector_contains p hj')
end VG.Proof.MlDsa.AArch64.Arith.Neon
