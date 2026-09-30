import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.X25519.Bytes

/-! Untrusted: reuse the shared little-endian memory lemmas. -/

namespace VG.Proof.Ed25519

open VG VG.Spec.Ed25519

theorem decodeLE_eq (xs : List Byte) : decodeLE xs = Proof.X25519.leNum xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [decodeLE, Proof.X25519.leNum, ih]

theorem decodeLE_append (xs ys : List Byte) :
    decodeLE (xs ++ ys) = decodeLE xs + 256 ^ xs.length * decodeLE ys := by
  simp only [decodeLE_eq, Proof.X25519.leNum_append]

theorem decodeLE_lt (xs : List Byte) : decodeLE xs < 256 ^ xs.length := by
  rw [decodeLE_eq]; exact Proof.X25519.leNum_lt xs

end VG.Proof.Ed25519
