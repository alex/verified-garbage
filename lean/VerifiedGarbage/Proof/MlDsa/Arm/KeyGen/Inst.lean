import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Top
import VerifiedGarbage.Impl.MlDsa.Arm.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBounded
import VerifiedGarbage.Proof.MlDsa.Arm.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.BitPack

/-!
# ML-DSA key generation on 32-bit ARM, with this library's primitives

Untrusted: everything here is checked by Lean. The ARM implementations of
the primitives (`prims`) are verified with at most 28 bytes of stack, and
their frames use no more (`prims_ok`), so key generation with them is
verified with 36 (`keyGen44_verified`, …).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm
open VG.Impl.MlDsa.Arm.KeyGen

theorem prims_ok : PrimsOk prims 28 where
  ntt := ⟨⟨28, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨28, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨24, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨24, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  add := ⟨⟨0, by decide, Arith.AddSub.add_verified⟩, by decide +kernel⟩
  rejNtt := ⟨⟨8, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  rejBounded := ⟨⟨8, by decide, Sample.rejBounded_verified⟩, by decide +kernel⟩
  power2Round := ⟨⟨4, by decide, Round.P2R.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitPack := ⟨⟨4, by decide, Pack.bitPack_verified⟩, by decide +kernel⟩

theorem keyGen44_verified :
    Verified Arm.target keyGen44 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 Arm.abi 36) :=
  keyGen_verified prims_ok _ (.inl rfl)

theorem keyGen65_verified :
    Verified Arm.target keyGen65 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 Arm.abi 36) :=
  keyGen_verified prims_ok _ (.inr (.inl rfl))

theorem keyGen87_verified :
    Verified Arm.target keyGen87 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 Arm.abi 36) :=
  keyGen_verified prims_ok _ (.inr (.inr rfl))

end VG.Proof.MlDsa.Arm.KeyGen
