import VerifiedGarbage.Spec.Ed25519
import VerifiedGarbage.Proof.X25519.Invert

/-! Intermediate values in RFC 8032 point decoding. -/

namespace VG.Proof.Ed25519

open VG.Spec.X25519

def rootU (y : Fe) : Fe := y * y - 1

def rootV (y : Fe) : Fe := Spec.Ed25519.d * y * y + 1

def rootX (y : Fe) : Fe :=
  rootU y * pow (rootV y) 3 * pow (rootU y * pow (rootV y) 7) ((P - 5) / 8)

open VG.Proof.X25519 in
theorem pow_three (v : Fe) : v * v * v = pow v 3 := by
  rw [pow_pw]; conv => lhs; rw [← pw_one v]
  simp only [pw_mul]

open VG.Proof.X25519 in
theorem pow_seven (v : Fe) : (v * v * v) * (v * v * v) * v = pow v 7 := by
  rw [pow_pw]; conv => lhs; rw [← pw_one v]
  simp only [pw_mul]

end VG.Proof.Ed25519
