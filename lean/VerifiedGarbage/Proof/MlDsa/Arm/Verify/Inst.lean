import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Top
import VerifiedGarbage.Impl.MlDsa.Arm.Verify.Inst
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.BallCT
import VerifiedGarbage.Proof.MlDsa.Arm.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.Arm.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintUnpackCT

/-!
# ML-DSA verification on 32-bit ARM, with this library's primitives

The ARM implementations of the primitives (`prims`) are verified with at most
28 bytes of stack, and their frames use no more (`prims_ok`), so verification
with them is verified with 36 (`verify44_verified`, …).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm
open VG.Impl.MlDsa.Arm.Verify

theorem prims_ok : VPrimsOk prims 28 where
  ntt := ⟨⟨28, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨28, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨24, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨24, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  sub := ⟨⟨0, by decide, Arith.AddSub.sub_verified⟩, by decide +kernel⟩
  rejNtt := ⟨⟨8, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  ball := ⟨⟨8, by decide, Sample.sampleInBall_verified⟩, by decide +kernel⟩
  useHint := ⟨⟨12, by decide, Round.UseHint.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitUnpack := ⟨⟨4, by decide, Pack.bitUnpack_verified⟩, by decide +kernel⟩
  unpackT1 := ⟨⟨0, by decide, Pack.unpackT1_verified⟩, by decide +kernel⟩
  hintUnpack := ⟨⟨16, by decide, Pack.Hint.hintBitUnpack_verified⟩, by decide +kernel⟩
  normLt := ⟨⟨4, by decide, Round.NormLt.verified⟩, by decide +kernel⟩

theorem verify44_verified :
    Verified Arm.target verify44 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa44 Arm.abi 36) :=
  verify_verified prims_ok _ (.inl rfl)

theorem verify65_verified :
    Verified Arm.target verify65 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa65 Arm.abi 36) :=
  verify_verified prims_ok _ (.inr (.inl rfl))

theorem verify87_verified :
    Verified Arm.target verify87 (Spec.MlDsa.verifyContract Spec.MlDsa.mlDsa87 Arm.abi 36) :=
  verify_verified prims_ok _ (.inr (.inr rfl))

end VG.Proof.MlDsa.Arm.Verify
