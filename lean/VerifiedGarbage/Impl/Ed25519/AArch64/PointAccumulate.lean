import VerifiedGarbage.Impl.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Impl.Ed25519.AArch64.PointTable

/-! A descending scalar bit: add its power and select with the bit mask. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def scalarBitMask : List Instr :=
  [.add .x .x8 .x19 .x1, .add .x .x8 .x0 .x8, .ldrb .x3 .x8 768, .subImm .x .x3 .x3 1]

def prepareAdd : List Instr :=
  savePoint ++ tableAddr 5376 ++ pointFromTable ++ copyPointToQ ++ restorePoint

def pointAccumulate : List Instr := prepareAdd ++ pointAdd ++ scalarBitMask ++ pointSelect

end VG.Impl.Ed25519.AArch64
