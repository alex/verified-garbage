import VerifiedGarbage.Impl.Ed25519.Arm.PointBatch
import VerifiedGarbage.Impl.Ed25519.Arm.BatchBits

/-! Scalar multiplication with sixteen-bit batches and compact checkpoints.
The scalar pointer is saved at offset 52; the batch count is public. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def batchStart : List Instr :=
  [.ldr .r11 .r0 56, .dp .sub .r11 .r11 (.imm 1), .str .r11 .r0 56]

def batchTest : List Instr := [.ldr .r11 .r0 56, .cmp .r11 (.imm 0)]

def pointMulBody : Prog isa :=
  .seq (.block batchStart) (.seq prepareBatch
    (.seq (.block batchBits) (.seq accumulate16 (.block batchTest))))

def pointMultiply (count : Nat) : Prog isa :=
  .seq (pointPowers 1600 count true)
    (.seq (constPoint Spec.Ed25519.identity)
      (.seq (.block [.movw .r11 (BitVec.ofNat 16 count), .str .r11 .r0 56])
        (.loop pointMulBody .ne)))

end VG.Impl.Ed25519.Arm
