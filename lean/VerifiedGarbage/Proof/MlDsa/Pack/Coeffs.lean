import VerifiedGarbage.Proof.MlDsa.Pack.Mem

/-!
# ML-DSA: coefficients written in order, for every target

A loop that writes the coefficients of a polynomial of `[u32; 256]` one after
the other: after `t` of them, coefficient `i` is `G i` for `i < t` and what it
was before otherwise (`CoeffsUpTo`), until all 256 are written; and the bytes
of the words of a polynomial, from the words.
-/

namespace VG.Proof.MlDsa.Pack

open VG.Spec.MlDsa

theorem coeffAt_writeW_self (m : Mem) (p : Addr) (i : Nat) (v : BitVec 32) :
    coeffAt (m.writeW (coeffAddr p i) v) p i = v :=
  Mem.readW_writeW_self32 m _ v

/-- Writing coefficient `j` of the polynomial at `p`. -/
theorem coeffAt_writeW (m : Mem) (p : Addr) {i j : Nat} (hi : i < 2 ^ 62) (hj : j < 2 ^ 62) (v : BitVec 32) :
    coeffAt (m.writeW (coeffAddr p j) v) p i = if j = i then v else coeffAt m p i := by
  split
  · subst j; exact coeffAt_writeW_self m p i v
  · exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- The coefficients at `p`: the first `t` of them are `G`'s, the others `old`'s. -/
def CoeffsUpTo (m : Mem) (p : Addr) (t : Nat) (G old : Nat → BitVec 32) : Prop :=
  ∀ i < 256, coeffAt m p i = if i < t then G i else old i

theorem CoeffsUpTo.zero {m : Mem} {p : Addr} (G : Nat → BitVec 32) :
    CoeffsUpTo m p 0 G fun i => coeffAt m p i := fun i _ => by
  rw [ite_eq_right (Nat.not_lt_zero i)]

/-- Writing coefficient `t`. -/
theorem CoeffsUpTo.write {m : Mem} {p : Addr} {t : Nat} {G old : Nat → BitVec 32}
    (h : CoeffsUpTo m p t G old) (ht : t < 256) {v : BitVec 32} (hv : v = G t) :
    CoeffsUpTo (m.writeW (coeffAddr p t) v) p (t + 1) G old := fun i hi => by
  rw [coeffAt_writeW m p (by omega) (by omega)]
  by_cases e : t = i
  · subst e; rw [ite_eq_left rfl, ite_eq_left (by omega), hv]
  · rw [ite_eq_right e, h i hi]
    by_cases hit : i < t
    · rw [ite_eq_left hit, ite_eq_left (by omega)]
    · rw [ite_eq_right hit, ite_eq_right (by omega)]

/-- All 256 coefficients written. -/
theorem CoeffsUpTo.all {m : Mem} {p : Addr} {G old : Nat → BitVec 32} (h : CoeffsUpTo m p 256 G old)
    {i : Nat} (hi : i < 256) : coeffAt m p i = G i := by
  rw [h i hi, ite_eq_left hi]

/-- The bytes of words that agree. -/
theorem bytes_of_words {m₁ m₂ : Mem} {p : Addr} {N : Nat}
    (h : (List.range N).map (fun i => (coeffAt m₁ p i).toNat) = (List.range N).map (fun i => (coeffAt m₂ p i).toNat))
    {a : Addr} (ha : (⟨p, N * 4⟩ : Region).Contains a 1) : m₁ a = m₂ a := by
  simp only [Region.Contains] at ha
  have hw : ∀ i < N, coeffAt m₁ p i = coeffAt m₂ p i := fun i hi =>
    BitVec.eq_of_toNat_eq (List.map_inj_left.mp h i (List.mem_range.mpr hi))
  have hi : (a - p).toNat / 4 < N := by omega
  have ht : (a - p).toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have ea : a = coeffAddr p ((a - p).toNat / 4) + BitVec.ofNat 64 ((a - p).toNat % 4) := by
    rw [coeffAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ea, Mem.readW_byte m₁ (coeffAddr p _) ht, Mem.readW_byte m₂ (coeffAddr p _) ht, ← coeffAt_eq, ← coeffAt_eq,
    hw _ hi]

end VG.Proof.MlDsa.Pack
