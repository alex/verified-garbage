import VerifiedGarbage.Spec.Ed25519
import VerifiedGarbage.Proof.X25519.Invert

/-! Intermediate values in RFC 8032 point decoding. -/

namespace VG.Proof.Ed25519

open VG.Spec.X25519
open Fin.CommRing

def rootU (y : Fe) : Fe := y * y - 1

def rootV (y : Fe) : Fe := Spec.Ed25519.d * y * y + 1

def rootX (y : Fe) : Fe :=
  rootU y * pow (rootV y) 3 * pow (rootU y * pow (rootV y) 7) ((P - 5) / 8)

theorem pow_three (v : Fe) : v * v * v = pow v 3 := by
  rw [VG.Proof.X25519.pow_eq]; ring

theorem pow_seven (v : Fe) : (v * v * v) * (v * v * v) * v = pow v 7 := by
  rw [VG.Proof.X25519.pow_eq]; ring

end VG.Proof.Ed25519
