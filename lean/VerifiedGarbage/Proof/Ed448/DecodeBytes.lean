import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X448.Field

/-!
# Ed448: decoding a point, from its bytes

`decodePoint` of 57 bytes, in terms of what code computes: the number `y₀` of
the first 56 bytes and the last byte `b`. The encoding's `y` (its bits
0–454) is below `p` exactly when bits 0–6 of `b` are 0 and `y₀ < p`, and the
sign is bit 7 of `b`. Stated here, without Mathlib, where `2 ^ 455` is the
specification's term.
-/

namespace VG.Proof.Ed448

open VG.Spec.Ed448 (decodeLE)
open VG.Proof.X448 (toFe)

theorem decodeLE_57 (bs : List Byte) (h : bs.length = 57) :
    decodeLE bs = decodeLE (bs.take 56) + 256 ^ 56 * (bs.getD 56 0).toNat := by
  have e : bs = bs.take 56 ++ [bs.getD 56 0] := by
    conv => lhs; rw [← List.take_append_drop 56 bs]
    congr 1
    apply List.ext_getElem
    · simp [h]
    · intro i h1 h2
      simp only [List.length_drop, h] at h1
      simp only [List.getElem_drop, List.length_singleton] at h2 ⊢
      have : i = 0 := by omega
      subst this
      simp [List.getD_eq_getElem?_getD, h]
  conv => lhs; rw [e]
  rw [decodeLE_append]
  simp [decodeLE, List.length_take, h]

theorem decodePoint_bytes (bs : List Byte) (h : bs.length = 57) :
    Spec.Ed448.decodePoint bs =
      if (bs.getD 56 0).toNat % 128 = 0 ∧ decodeLE (bs.take 56) < Spec.X448.P then
        (Spec.Ed448.recoverX (toFe (decodeLE (bs.take 56))) ((bs.getD 56 0).toNat / 128 == 1)).map
          fun x => ⟨x, toFe (decodeLE (bs.take 56)), 1⟩
      else none := by
  have hy0 : decodeLE (bs.take 56) < 256 ^ 56 := by
    have := decodeLE_lt' (bs.take 56)
    rwa [List.length_take, h] at this
  have hb : (bs.getD 56 0).toNat < 256 := (bs.getD 56 0).isLt
  have hP : Spec.X448.P < 256 ^ 56 := by decide +kernel
  have e455 : (2 : Nat) ^ 455 = 256 ^ 56 * 128 := by decide +kernel
  generalize hy : decodeLE (bs.take 56) = y0 at *
  generalize hbb : (bs.getD 56 0).toNat = b at *
  unfold Spec.Ed448.decodePoint
  rw [decodeLE_57 bs h, hy, hbb, h]
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
  rw [e455]
  generalize (256 : Nat) ^ 56 = M at *
  have hM : 0 < M := by omega
  have em : (y0 + M * b) % (M * 128) = y0 + M * (b % 128) := by
    rw [Nat.add_mod, show M * b % (M * 128) = M * (b % 128) from Nat.mul_mod_mul_left M b 128]
    rw [Nat.mod_eq_of_lt (by omega : y0 < M * 128)]
    have : b % 128 < 128 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_of_lt]
    have : M * (b % 128) ≤ M * 127 := Nat.mul_le_mul_left M (by omega)
    omega
  have ed : (y0 + M * b) / (M * 128) = b / 128 := by
    rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hy0, Nat.zero_add]
  by_cases hc : b % 128 = 0 ∧ y0 < Spec.X448.P
  · rw [ite_eq_left hc]
    have hl : (y0 + M * b) % (M * 128) < Spec.X448.P := by
      rw [em, hc.1, Nat.mul_zero, Nat.add_zero]; exact hc.2
    rw [dite_eq_left hl]
    have hfe : (⟨(y0 + M * b) % (M * 128), hl⟩ : Spec.X448.Fe) = toFe y0 :=
      Fin.ext (by
        show (y0 + M * b) % (M * 128) = y0 % Spec.X448.P
        rw [em, hc.1, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hc.2])
    rw [hfe, ed]
    cases Spec.Ed448.recoverX (toFe y0) (b / 128 == 1) <;> rfl
  · rw [ite_eq_right hc]
    have hl : ¬ (y0 + M * b) % (M * 128) < Spec.X448.P := by
      rw [em]
      intro h'
      apply hc
      rcases Nat.eq_zero_or_pos (b % 128) with h0 | h0
      · rw [h0, Nat.mul_zero, Nat.add_zero] at h'; exact ⟨h0, h'⟩
      · have : M ≤ M * (b % 128) := Nat.le_mul_of_pos_right M h0
        omega
    rw [dite_eq_right hl]

end VG.Proof.Ed448
