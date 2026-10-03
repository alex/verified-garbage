import VerifiedGarbage.Proof.X448.Wide.Term

/-! Untrusted: two-word coefficients in the existing X448 scratch region. -/
namespace VG.Proof.X448.Wide

open VG VG.AArch64 VG.Proof.X448.AArch64

abbrev coeff (m : Mem) (base : Addr) (o i : Nat) : Nat :=
  pair (word m base (o + 16 * i)) (word m base (o + 16 * i + 8))

def putCoeff (m : Mem) (base : Addr) (o i : Nat) (lo hi : BitVec 64) : Mem :=
  (m.writeW (off base (o + 16 * i)) lo).writeW (off base (o + 16 * i + 8)) hi

theorem putCoeff_outside (m : Mem) (base : Addr) {o i : Nat} (lo hi : BitVec 64)
    (h : o + 16 * i + 16 ≤ 8192) :
    Outside base (o + 16 * i) 16 m (putCoeff m base o i lo hi) := by
  exact ((writeW_outside m base lo (by omega)).mono (by omega) (by omega)).trans
    ((writeW_outside _ base hi (by omega)).mono (by omega) (by omega))

theorem coeff_put (m : Mem) (base : Addr) {o i j : Nat} (lo hi : BitVec 64)
    (hi' : o + 16 * i + 16 ≤ 8192) (hj : o + 16 * j + 16 ≤ 8192) :
    coeff (putCoeff m base o i lo hi) base o j =
      if j = i then pair lo hi else coeff m base o j := by
  unfold coeff putCoeff
  have e0 : o + 16 * i = o + 8 * (2 * i) := by omega
  have e1 : o + 16 * i + 8 = o + 8 * (2 * i + 1) := by omega
  have e2 : o + 16 * j = o + 8 * (2 * j) := by omega
  have e3 : o + 16 * j + 8 = o + 8 * (2 * j + 1) := by omega
  rw [e1, e0, e3, e2]
  rw [word_write _ base (by omega) (by omega), word_write _ base (by omega) (by omega)]
  rw [ite_eq_right (by omega : 2 * j ≠ 2 * i + 1)]
  rw [word_write _ base (by omega) (by omega)]
  by_cases h : j = i
  · subst j
    simp only [ite_true]
  · simp only [h, show 2 * j ≠ 2 * i by omega, show 2 * j + 1 ≠ 2 * i + 1 by omega,
      ite_false]
    rw [word_write _ base (by omega) (by omega), ite_eq_right (by omega : 2 * j + 1 ≠ 2 * i)]

theorem outside_coeff {base : Addr} {o n d : Nat} {m m' : Mem}
    (h : Outside base o n m m') (hd : d + 16 ≤ o ∨ o + n ≤ d)
    (hd' : d + 16 ≤ 8192) :
    pair (word m' base d) (word m' base (d + 8)) =
      pair (word m base d) (word m base (d + 8)) := by
  rw [h.word (by omega) (by omega), h.word (by omega) (by omega)]

end VG.Proof.X448.Wide
