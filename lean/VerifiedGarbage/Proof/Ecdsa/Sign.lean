import VerifiedGarbage.Proof.Weierstrass.Complete
import VerifiedGarbage.Spec.Ecdsa

/-!
# ECDSA signing from the values an implementation computes

`signWith_eq`: if an implementation has a projective representative
`(X : Y : Z)` over `Fin p` of `[k]G`, the integer `x < p` of `X Z^(p-2)`,
`r = x mod n`, an `s < n` congruent to `k^(n-2) (e + r d)` modulo `n`, and
computes the
flag "`d`, `k` in `[1, n-1]`, `r ≠ 0`, `s ≠ 0`", then the specification's
signature is `(r, s)` if the flag is set, and none otherwise.
-/

namespace VG.Proof.Ecdsa

open Spec.Weierstrass Spec.Ecdsa Proof.Weierstrass

variable {C : Curve}

theorem signWith_eq (hC : Good C) {d e k : Nat} {X Y Z : Fe C} (hR : Rep C X Y Z (mul k (G C)))
    {x : Nat} (hx : x < C.p) (hxX : Fin.ofNat C.p x = X * Z ^ (C.p - 2))
    {s : Nat} (hs : s < C.n)
    (hsv : Fin.ofNat C.n s =
      Fin.ofNat C.n k ^ (C.n - 2) * (Fin.ofNat C.n e + Fin.ofNat C.n (x % C.n) * Fin.ofNat C.n d)) :
    signWith C d e k = if 1 ≤ d ∧ d < C.n ∧ 1 ≤ k ∧ k < C.n ∧ x % C.n ≠ 0 ∧ s ≠ 0
      then some (x % C.n, s) else none := by
  unfold signWith
  by_cases hv : 1 ≤ d ∧ d < C.n ∧ 1 ≤ k ∧ k < C.n
  · simp only [hv, and_self, ite_true]
    generalize hP : mul k (G C) = P at hR
    cases P with
    | infinity =>
      have h0 : x = 0 := by
        have h := congrArg Fin.val (hxX.trans hR.infinity_x)
        rwa [Fin.val_ofNat, Nat.mod_eq_of_lt hx] at h
      simp only [h0, Nat.zero_mod, ne_eq, not_true_eq_false, false_and, and_false, ite_false]
    | affine xR yR =>
      have hxr : xR.val = x := by
        have h := congrArg Fin.val ((hR.x_eq hC).trans hxX.symm)
        rwa [Fin.val_ofNat, Nat.mod_eq_of_lt hx] at h
      simp only [hxr]
      have hsv' : pow (Fin.ofNat C.n k) (C.n - 2) *
          (Fin.ofNat C.n e + Fin.ofNat C.n (x % C.n) * Fin.ofNat C.n d) = ⟨s, hs⟩ := by
        rw [pow_eq_npow, ← hsv]
        exact Fin.ext (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt hs])
      rw [hsv']
      simp only [Fin.ext_iff, Fin.val_zero]
      by_cases h1 : x % C.n = 0
      · simp [h1]
      · by_cases h2 : s = 0
        · simp [h1, h2]
        · simp [h1, h2]
  · have hv' : ¬(1 ≤ d ∧ d < C.n ∧ 1 ≤ k ∧ k < C.n ∧ x % C.n ≠ 0 ∧ s ≠ 0) :=
      fun h => hv ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
    simp only [hv, hv', ite_false]

end VG.Proof.Ecdsa
