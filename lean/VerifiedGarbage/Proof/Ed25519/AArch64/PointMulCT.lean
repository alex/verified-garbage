import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMul

/-! Untrusted: what a multiplication's constant-time proof assumes of its scalar. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def MulCTPreN (count : Nat) (base : Addr) (scalar : Nat) (s : State) : Prop :=
  Scr s base ∧ scalar < 2 ^ (16 * count) ∧ env s.mem base 16 = Spec.Ed25519.d ∧
    ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)

abbrev MulCTPre := MulCTPreN 16

end VG.Proof.Ed25519.AArch64
