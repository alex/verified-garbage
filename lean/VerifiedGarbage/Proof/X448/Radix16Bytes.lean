import VerifiedGarbage.Proof.X448.Radix16
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# X448: byte encoding of 16-bit limbs

Each limb is two bytes, least significant first, with all 448 input bits
retained.
-/

namespace VG.Proof.X448.Radix16

open VG VG.Spec.X448
open VG.Proof.X25519 (leNum leNum_append leBytes)

def byteN (m : Mem) (p : Addr) (i : Nat) : Nat := (m (p + BitVec.ofNat 64 i)).toNat

def decoded (m : Mem) (p : Addr) (k : Nat) : Nat :=
  byteN m p (2 * k) + 256 * byteN m p (2 * k + 1)

theorem bytesAt_succ (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (n + 1) = m p :: bytesAt m (p + 1) n :=
  VG.Proof.X25519.bytesAt_succ m p n

theorem decoded_val (m : Mem) (p : Addr) :
    ∀ n, leNum (bytesAt m p (2 * n)) = valN (decoded m p) n
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 2 from rfl, bytesAt_add, leNum_append, decoded_val m p n,
      valN_succ, length_bytesAt, show (256 : Nat) ^ (2 * n) = radix ^ n by rw [Nat.pow_mul]; rfl]
    apply congrArg (valN (decoded m p) n + radix ^ n * ·)
    rw [bytesAt_succ, bytesAt_succ,
      show bytesAt m (p + BitVec.ofNat 64 (2 * n) + 1 + 1) 0 = [] from rfl]
    simp only [leNum, decoded, byteN, Nat.mul_zero, Nat.add_zero]
    rw [Offset.add_ofNat_add_one]

theorem decoded_lt (m : Mem) (p : Addr) (k : Nat) : decoded m p k < radix := by
  have h0 := (m (p + BitVec.ofNat 64 (2 * k))).isLt
  have h1 := (m (p + BitVec.ofNat 64 (2 * k + 1))).isLt
  simp only [decoded, byteN, radix]
  omega

theorem decode_val (m : Mem) (p : Addr) :
    valN (decoded m p) 28 = decodeUCoordinate (bytesAt m p 56) := by
  rw [decodeUCoordinate_eq (length_bytesAt m p 56)]
  exact (decoded_val m p 28).symm

theorem packed_bytes {m : Mem} {p : Addr} {f : Nat → Nat}
    (h : ∀ i < 28, decoded m p i = f i) : bytesAt m p 56 = leBytes 56 (valN f 28) := by
  have hv : leNum (bytesAt m p 56) = valN f 28 :=
    (decoded_val m p 28).trans (valN_congr h)
  have out : bytesAt m p 56 = leBytes 56 (m.read p 56).toNat :=
    VG.Proof.X25519.bytesAt_leBytes m p 56
  rw [← leNum_bytesAt_read, hv] at out
  exact out

end VG.Proof.X448.Radix16
