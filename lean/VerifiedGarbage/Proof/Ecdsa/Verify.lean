import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Spec.Ecdsa.Verify

/-!
# ECDSA signature verification from the values an implementation computes

`verify_eq`: the specification's verification of the signature `(r, s)` of
the hash integer `e` with the public key `bs` (`04 ‖ x ‖ y`), from
* `u` and `v` below `n`, congruent to `e s^(n-2)` and `r s^(n-2)` modulo `n`;
* a representative `(X : Y : Z)` over `Fin p` of `[u]G + [v]P`, where `P` is
  the key's point whenever the key is valid (`Ecdh.Valid`, as the code
  checks it);
* the number `x < p` of `X Z^(p-2)`.

The signature is valid exactly if the key is, `r` and `s` are in
`[1, n-1]`, `Z ≠ 0` and `x ≡ r` modulo `n`.
-/

namespace VG.Proof.Ecdsa

open Spec.Weierstrass Spec.EcKey Spec.Ecdsa VG.Proof.Weierstrass VG.Proof.EcKey VG.Proof.Ecdh

variable {C : Curve}

theorem verify_eq (hC : Good C) {bs : List Byte} (hlen : bs.length = 2 * C.len + 1) {b0 : Byte}
    (hb0 : bs.head? = some b0) {x y : Nat} (hxv : ofBytes ((bs.drop 1).take C.len) = x)
    (hyv : ofBytes (bs.drop (C.len + 1)) = y) {P : Point C}
    (hP : ∀ h : Valid C b0 x y, P = .affine ⟨x, h.2.1⟩ ⟨y, h.2.2.1⟩)
    {e r s : Nat} {sig : List Byte} (hr : ofBytes (sig.take C.len) = r)
    (hs : ofBytes (sig.drop C.len) = s) {u v : Nat} (hu : u < C.n) (hv : v < C.n)
    (hue : Fin.ofNat C.n u = Fin.ofNat C.n e * Fin.ofNat C.n s ^ (C.n - 2))
    (hve : Fin.ofNat C.n v = Fin.ofNat C.n r * Fin.ofNat C.n s ^ (C.n - 2))
    {X Y Z : Fe C} (hR : Rep C X Y Z (add (mul u (G C)) (mul v P))) {xo : Nat} (hxo : xo < C.p)
    (hxoX : Fin.ofNat C.p xo = X * Z ^ (C.p - 2)) :
    verify C bs e sig = decide (Valid C b0 x y ∧ (1 ≤ r ∧ r < C.n) ∧ (1 ≤ s ∧ s < C.n) ∧ Z ≠ 0 ∧
      Fin.ofNat C.n xo = Fin.ofNat C.n r) := by
  unfold verify
  rw [decode_eq hlen hb0 hxv hyv, hr, hs]
  by_cases hV : Valid C b0 x y
  · rw [dite_eq_left hV]
    simp only [hV, true_and]
    rw [← hP hV]
    unfold verifyWith
    by_cases hrs : 1 ≤ r ∧ r < C.n ∧ 1 ≤ s ∧ s < C.n
    · rw [ite_eq_left hrs]
      have hu' : Fin.ofNat C.n e * pow (Fin.ofNat C.n s) (C.n - 2) = ⟨u, hu⟩ := by
        rw [pow_eq_npow, ← hue]
        exact Fin.ext (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt hu])
      have hv' : Fin.ofNat C.n r * pow (Fin.ofNat C.n s) (C.n - 2) = ⟨v, hv⟩ := by
        rw [pow_eq_npow, ← hve]
        exact Fin.ext (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt hv])
      simp only [hu', hv']
      generalize hQ : add (mul u (G C)) (mul v P) = Q at hR
      cases Q with
      | infinity =>
        have hZ : Z = 0 := hR.z_eq_zero_iff.mpr rfl
        simp only [hZ, ne_eq, not_true_eq_false, false_and, and_false, decide_false]
      | affine xR yR =>
        have hZ : Z ≠ 0 := fun h => nomatch hR.z_eq_zero_iff.mp h
        have hxr : xR.val = xo := by
          have h := congrArg Fin.val ((hR.x_eq hC).trans hxoX.symm)
          rwa [Fin.val_ofNat, Nat.mod_eq_of_lt hxo] at h
        have hc : (xo % C.n == r) = decide (Fin.ofNat C.n xo = Fin.ofNat C.n r) := by
          have : Fin.ofNat C.n xo = Fin.ofNat C.n r ↔ xo % C.n = r := by
            rw [Fin.ext_iff, Fin.val_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt hrs.2.1]
          rw [Bool.beq_eq_decide_eq, decide_eq_decide]
          exact this.symm
        simp only [hxr, hc, hZ, ne_eq, not_false_eq_true, true_and]
        simp only [hrs, and_self, true_and]
    · rw [ite_eq_right hrs]
      have : ¬((1 ≤ r ∧ r < C.n) ∧ (1 ≤ s ∧ s < C.n) ∧ Z ≠ 0 ∧ Fin.ofNat C.n xo = Fin.ofNat C.n r) :=
        fun h => hrs ⟨h.1.1, h.1.2, h.2.1.1, h.2.1.2⟩
      exact (decide_eq_false this).symm
  · rw [dite_eq_right hV]
    exact (decide_eq_false fun h => hV h.1).symm

end VG.Proof.Ecdsa
