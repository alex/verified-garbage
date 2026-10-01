import VerifiedGarbage.Impl.Ed25519.Arm.Packed
import VerifiedGarbage.Impl.Ed25519.Arm.PointLoop

/-! Checkpoints and adjacent powers, using public loop bounds. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def tableAddr (start : Nat) : List Instr :=
  [.movw .r3 (BitVec.ofNat 16 start), .dp .add .r12 .r0 (.reg .r3),
    .dp .add .r12 .r12 (.shifted .r11 .lsl 7)]

def powersNext (count : Nat) : List Instr :=
  [.movw .r3 (BitVec.ofNat 16 count), .dp .add .r11 .r11 (.imm 1), .cmp .r11 (.reg .r3)]

def powerStride (batch : Bool) : Nat := if batch then 16 else 1
def powerBatch (batch : Bool) : Prog isa := if batch then double16 else pointDouble

def powersBody (start count : Nat) (batch : Bool := true) : Prog isa :=
  .seq (.block (tableAddr start ++ pointToTable))
    (.seq (powerBatch batch) (.block (powersNext count)))

def pointPowers (start count : Nat) (batch : Bool := true) : Prog isa :=
  .seq (.block [.movw .r11 0]) (.loop (powersBody start count batch) .ne)

end VG.Impl.Ed25519.Arm
