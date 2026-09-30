import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.X25519.Field

/-! Untrusted: the length and canonical-coordinate branches of point decoding. -/

namespace VG.Proof.Ed25519

open VG VG.Spec.X25519

theorem toFe_of_lt (n : Nat) (h : n < P) : Proof.X25519.toFe n = (⟨n, h⟩ : Fe) := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt h

private theorem bindPoint (o : Option Fe) (y : Fe) :
    (do let x ← o; pure (⟨x, y, 1, x * y⟩ : Spec.Ed25519.Point)) =
      o.map (fun x => (⟨x, y, 1, x * y⟩ : Spec.Ed25519.Point)) := by
  cases o <;> rfl

theorem decodePoint32 (bs : List Byte) (hl : bs.length = 32) :
    Spec.Ed25519.decodePoint bs =
      if Spec.Ed25519.decodeLE bs % 2 ^ 255 < P then
        (Spec.Ed25519.recoverX (Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255))
          (Spec.Ed25519.decodeLE bs / 2 ^ 255 == 1)).map (fun x =>
            (⟨x, Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255), 1,
              x * Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255)⟩ : Spec.Ed25519.Point))
      else none := by
  unfold Spec.Ed25519.decodePoint
  simp only [hl, show (32 != 32) = false by decide, Bool.false_eq_true, ite_false]
  by_cases h : Spec.Ed25519.decodeLE bs % 2 ^ 255 < P
  · rw [dite_eq_left h, ite_eq_left h, toFe_of_lt _ h]
    exact bindPoint _ _
  · rw [dite_eq_right h, ite_eq_right h]

end VG.Proof.Ed25519
