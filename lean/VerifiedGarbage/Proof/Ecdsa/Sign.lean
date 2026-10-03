import VerifiedGarbage.Proof.Weierstrass.Complete
import VerifiedGarbage.Spec.Ecdsa

/-!
# ECDSA signing from the values an implementation computes

`signWith_eq`: if an implementation has a projective representative
`(X : Y : Z)` of `[k]G`, the integer `x < p` of `X Z^(p-2)`, `r = x mod n`,
an `s < n` congruent to `k^(n-2) (e + r d)` modulo `n`, and computes the
flag "`d`, `k` in `[1, n-1]`, `r ≠ 0`, `s ≠ 0`", then the specification's
signature is `(r, s)` if the flag is set, and none otherwise.
-/

namespace VG.Proof.Ecdsa

open Spec.Weierstrass Spec.Ecdsa Proof.Weierstrass

variable {C : Curve} [Fact C.p.Prime]

theorem signWith_eq {d e k : Nat} {X Y Z : ZMod C.p} (hR : Rep C X Y Z (mul k (G C)))
    {x : Nat} (hx : x < C.p) (hxX : (x : ZMod C.p) = X * Z ^ (C.p - 2))
    {s : Nat} (hs : s < C.n)
    (hsv : (s : ZMod C.n) = (k : ZMod C.n) ^ (C.n - 2) * ((e : ZMod C.n) + ((x % C.n : Nat) : ZMod C.n) * d)) :
    signWith C d e k = if 1 ≤ d ∧ d < C.n ∧ 1 ≤ k ∧ k < C.n ∧ x % C.n ≠ 0 ∧ s ≠ 0
      then some (x % C.n, s) else none := by
  unfold signWith
  by_cases hv : 1 ≤ d ∧ d < C.n ∧ 1 ≤ k ∧ k < C.n
  · simp only [hv, and_self, ite_true]
    -- The spec's `s`, as an element of `ZMod n`.
    have hS : ∀ r : Nat, toF (pow (Fin.ofNat C.n k) (C.n - 2) *
        (Fin.ofNat C.n e + Fin.ofNat C.n r * Fin.ofNat C.n d)) =
        (k : ZMod C.n) ^ (C.n - 2) * ((e : ZMod C.n) + (r : ZMod C.n) * d) := by
      intro r
      rw [toF_mul, toF_pow, toF_add, toF_mul, toF_ofNat, toF_ofNat, toF_ofNat, toF_ofNat]
    generalize hP : mul k (G C) = P at hR
    cases P with
    | infinity =>
      have h0 : x = 0 := by
        have h := hR.infinity_x
        rw [← hxX] at h
        exact Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff _ _).mp h) hx
      simp only [h0, Nat.zero_mod, ne_eq, not_true_eq_false, false_and, and_false, ite_false]
    | affine xR yR =>
      have hxr : xR.val = x := by
        have h := hR.x_eq
        rw [← hxX, toF] at h
        exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h |>.trans (Nat.mod_eq_of_lt hx) |>.symm.trans
          (Nat.mod_eq_of_lt xR.isLt) |>.symm
      simp only [hxr]
      have hsv' : pow (Fin.ofNat C.n k) (C.n - 2) *
          (Fin.ofNat C.n e + Fin.ofNat C.n (x % C.n) * Fin.ofNat C.n d) = ⟨s, hs⟩ := by
        apply toF_injective
        rw [hS, ← hsv]; rfl
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
