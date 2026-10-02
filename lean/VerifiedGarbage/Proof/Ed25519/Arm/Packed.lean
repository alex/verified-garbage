import VerifiedGarbage.Impl.Ed25519.Arm.Packed
import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.WriteBytes

/-! The compact point-table representation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.X25519 (bytesAt)
open VG.Proof.X25519 (leNum leBytes leNum_append bytesAt_add bytesAt_succ length_bytesAt)

def byteN (m : Mem) (p : Addr) (i : Nat) : Nat := (m (p + BitVec.ofNat 64 i)).toNat
def packedLimb (m : Mem) (p : Addr) (k : Nat) : Nat :=
  byteN m p (2 * k) + 256 * byteN m p (2 * k + 1)
def packedV (m : Mem) (p : Addr) : Nat := val16 (packedLimb m p) 16
def packedF (m : Mem) (p : Addr) : Spec.X25519.Fe := VG.Proof.X25519.toFe (packedV m p)

theorem packedLimb_lt (m : Mem) (p : Addr) (k : Nat) : packedLimb m p k < 65536 := by
  have := (m (p + BitVec.ofNat 64 (2 * k))).isLt
  have := (m (p + BitVec.ofNat 64 (2 * k + 1))).isLt
  simp only [packedLimb, byteN]
  omega

theorem leNum_bytesAt2 (m : Mem) (p : Addr) :
    ∀ n, leNum (bytesAt m p (2 * n)) = val16 (packedLimb m p) n
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 2 from rfl, bytesAt_add, leNum_append, leNum_bytesAt2 m p n,
      val16_succ, length_bytesAt, show (256 : Nat) ^ (2 * n) = 2 ^ (16 * n) by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega]
    congr 2
    rw [bytesAt_succ, bytesAt_succ, show bytesAt m (p + BitVec.ofNat 64 (2 * n) + 1 + 1) 0 = [] from rfl]
    simp only [leNum, packedLimb, byteN, Nat.mul_zero, Nat.add_zero]
    rw [Offset.add_ofNat_add_one]

theorem byte_eq {v : BitVec 32} {n : Nat} (h : v.toNat = n) : v.setWidth 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, h]

theorem packedV_eq {m : Mem} {p : Addr} {f : Nat → Nat} (hl : ∀ k < 16, f k < 65536)
    (h0 : ∀ k < 16, m (p + BitVec.ofNat 64 (2 * k)) = BitVec.ofNat 8 (f k))
    (h1 : ∀ k < 16, m (p + BitVec.ofNat 64 (2 * k + 1)) = BitVec.ofNat 8 (f k / 256)) :
    packedV m p = val16 f 16 := by
  apply val16_congr
  intro k hk
  simp only [packedLimb, byteN, h0 k hk, h1 k hk, BitVec.toNat_ofNat]
  have := hl k hk
  omega

theorem packedV_frame {m m' : Mem} {p : Addr} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨p, 32⟩ : Region).Disjoint r) : packedV m' p = packedV m p := by
  apply val16_congr
  intro k hk
  simp only [packedLimb, byteN,
    hf.bytes hd (by decide : 32 ≤ 2 ^ 64) (by omega : 2 * k < 32),
    hf.bytes hd (by decide : 32 ≤ 2 ^ 64) (by omega : 2 * k + 1 < 32)]

end VG.Proof.Ed25519.Arm
