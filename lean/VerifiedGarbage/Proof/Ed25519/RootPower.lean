import VerifiedGarbage.Proof.X25519.Invert

/-! The decoding addition chain equals the RFC 8032 exponent. -/

namespace VG.Proof.Ed25519

open VG.Spec.X25519 VG.Proof.X25519
open Fin.CommRing

def rootPower (z : Fe) : Fe :=
  let t0 := z * z                 -- 2
  let t1 := sqn t0 2              -- 8
  let t1 := z * t1                -- 9
  let t0 := t0 * t1               -- 11
  let t2 := t0 * t0               -- 22
  let t1 := t1 * t2               -- 31 = 2^5 - 1
  let t2 := sqn t1 5
  let t1 := t2 * t1               -- 2^10 - 1
  let t2 := sqn t1 10
  let t2 := t2 * t1               -- 2^20 - 1
  let t3 := sqn t2 20
  let t2 := t3 * t2               -- 2^40 - 1
  let t2 := sqn t2 10
  let t1 := t2 * t1               -- 2^50 - 1
  let t2 := sqn t1 50
  let t2 := t2 * t1               -- 2^100 - 1
  let t3 := sqn t2 100
  let t2 := t3 * t2               -- 2^200 - 1
  let t2 := sqn t2 50
  let t1 := t2 * t1               -- 2^250 - 1
  let t1 := sqn t1 2
  t1 * z                          -- 2^252 - 3

theorem rootPower_eq (z : Fe) : rootPower z = pow z ((P - 5) / 8) := by
  rw [pow_eq, rootPower]
  simp only [sqn_eq, ← pow_mul, ← pow_add, ← pow_succ, ← pow_succ', ← pow_two, mul_comm z,
    ← pow_mul]
  congr 1

end VG.Proof.Ed25519
