import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Group.Double
import Mathlib.Tactic.Module

/-!
# Verification with windows: the arithmetic of the digits and the equation

Target-independent facts for verification's windowed multiplication: the bytes
of a little-endian scalar are its base-256 digits, each splits into two
nibbles, and the windows' result `[k]A - [S]B` equals `-R` exactly when the
specification's equation `[S]B = R + [k]A` holds.
-/

namespace VG.Proof.Ed25519

open Edwards

theorem decodeLE_byte : ∀ (bs : List Byte) (i : Nat),
    Spec.Ed25519.decodeLE bs / 256 ^ i % 256 = (bs.getD i 0).toNat
  | [], i => by simp [Spec.Ed25519.decodeLE]
  | b :: bs, 0 => by
    simp only [Spec.Ed25519.decodeLE, pow_zero, Nat.div_one, List.getD_cons_zero]
    have := b.isLt; omega
  | b :: bs, i + 1 => by
    rw [List.getD_cons_succ, ← decodeLE_byte bs i, Spec.Ed25519.decodeLE, pow_succ,
      Nat.mul_comm (256 ^ i), ← Nat.div_div_eq_div_mul]
    congr 2
    have := b.isLt; omega

theorem div_split (x i : Nat) : x / 256 ^ i = 256 * (x / 256 ^ (i + 1)) + x / 256 ^ i % 256 := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]; omega

theorem byte_split (K i : Nat) (b : Byte) (hb : (b.toNat) = K / 256 ^ i % 256) :
    K / 256 ^ i = 256 * (K / 256 ^ (i + 1)) + (16 * (b.toNat / 16) + b.toNat % 16) := by
  have := div_split K i; omega

theorem high_zero {S i : Nat} (hS : S < 256 ^ 32) (hi : 32 ≤ i) : S / 256 ^ i = 0 :=
  Nat.div_eq_of_lt (lt_of_lt_of_le hS (Nat.pow_le_pow_right (by decide) hi))

theorem decodeLE_lt32 (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) < 256 ^ 32 := by
  have h := decodeLE_lt (Spec.Ed25519.bytesAt m p 32)
  rwa [show (Spec.Ed25519.bytesAt m p 32).length = 32 by simp [Spec.Ed25519.bytesAt]] at h

theorem decodeLE_lt64 (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 64) < 256 ^ 64 := by
  have h := decodeLE_lt (Spec.Ed25519.bytesAt m p 64)
  rwa [show (Spec.Ed25519.bytesAt m p 64).length = 64 by simp [Spec.Ed25519.bytesAt]] at h

/-- The windows' sum, nibble by nibble: `16` times the sum so far plus the digits. -/
theorem window_step (A N : EPoint dZ) (K S i : Nat) (k s : Byte)
    (hk : k.toNat = K / 256 ^ i % 256) (hs : s.toNat = S / 256 ^ i % 256) :
    (16 : Nat) • ((16 : Nat) • ((K / 256 ^ (i + 1)) • A + (S / 256 ^ (i + 1)) • N) +
      (k.toNat / 16) • A + (s.toNat / 16) • N) + (k.toNat % 16) • A + (s.toNat % 16) • N =
      (K / 256 ^ i) • A + (S / 256 ^ i) • N := by
  rw [byte_split K i k hk, byte_split S i s hs]
  module

/-- The projective comparison reads only `X : Y : Z`. -/
theorem pointEqual_repP {p q : Spec.Ed25519.Point} {a b : EPoint dZ} (hp : RepP p a) (hq : RepP q b) :
    Spec.Ed25519.pointEqual p q = true ↔ a = b := by
  have hz : toZ p.Z * toZ q.Z ≠ 0 := mul_ne_zero hp.z hq.z
  simp only [Spec.Ed25519.pointEqual, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : toZ (p.X * q.Z) = toZ (q.X * p.Z) := congrArg toZ h1
    have e2 : toZ (p.Y * q.Z) = toZ (q.Y * p.Z) := congrArg toZ h2
    rw [toZ_mul, toZ_mul, hp.x, hq.x] at e1
    rw [toZ_mul, toZ_mul, hp.y, hq.y] at e2
    ext
    · exact mul_right_cancel₀ hz (by linear_combination e1)
    · exact mul_right_cancel₀ hz (by linear_combination e2)
  · rintro rfl
    refine ⟨toZ_inj.mp ?_, toZ_inj.mp ?_⟩
    · rw [toZ_mul, toZ_mul, hp.x, hq.x]; ring
    · rw [toZ_mul, toZ_mul, hp.y, hq.y]; ring

/-- The first of the projective comparisons: the `x` coordinates agree. -/
theorem repP_cross_x {p q : Spec.Ed25519.Point} {a b : EPoint dZ} (hp : RepP p a) (hq : RepP q b) :
    p.X * q.Z = q.X * p.Z ↔ a.x = b.x := by
  constructor
  · intro h
    have e : toZ (p.X * q.Z) = toZ (q.X * p.Z) := congrArg toZ h
    rw [toZ_mul, toZ_mul, hp.x, hq.x] at e
    exact mul_right_cancel₀ (mul_ne_zero hp.z hq.z) (by linear_combination e)
  · intro h
    exact toZ_inj.mp (by rw [toZ_mul, toZ_mul, hp.x, hq.x, h]; ring)

/-- The second: the `y` coordinates agree. -/
theorem repP_cross_y {p q : Spec.Ed25519.Point} {a b : EPoint dZ} (hp : RepP p a) (hq : RepP q b) :
    p.Y * q.Z = q.Y * p.Z ↔ a.y = b.y := by
  constructor
  · intro h
    have e : toZ (p.Y * q.Z) = toZ (q.Y * p.Z) := congrArg toZ h
    rw [toZ_mul, toZ_mul, hp.y, hq.y] at e
    exact mul_right_cancel₀ (mul_ne_zero hp.z hq.z) (by linear_combination e)
  · intro h
    exact toZ_inj.mp (by rw [toZ_mul, toZ_mul, hp.y, hq.y, h]; ring)

/-- The windows' result `P` is `-Q` exactly when `[S]B = R + [k]A`. -/
theorem window_equation {P Q R A : Spec.Ed25519.Point} {Aa Ra : EPoint dZ} {K S : Nat}
    (hA : Rep A Aa) (hR : Rep R Ra) (hP : RepP P (K • Aa + S • (-baseAff))) (hQ : RepP Q (-Ra)) :
    Spec.Ed25519.pointEqual P Q = Spec.Ed25519.pointEqual
      (Spec.Ed25519.pointMul S Spec.Ed25519.basePoint)
      (Spec.Ed25519.pointAdd R (Spec.Ed25519.pointMul K A)) := by
  rw [Bool.eq_iff_iff, pointEqual_repP hP hQ,
    pointEqual_rep (pointMul_rep S basePoint_rep) (pointAdd_rep hR (pointMul_rep K hA))]
  constructor
  · intro h
    have e : Ra = -(K • Aa + S • (-baseAff)) := by rw [h, neg_neg]
    rw [e]; module
  · intro h
    rw [smul_neg, h]; module

end VG.Proof.Ed25519
