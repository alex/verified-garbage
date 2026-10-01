import VerifiedGarbage.Impl.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Impl.Ed25519.AArch64.PointTable

/-! A descending scalar bit's mask, for selecting with it. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def scalarBitMask : List Instr :=
  [.add .x .x8 .x19 .x1, .add .x .x8 .x0 .x8, .ldrb .x3 .x8 768, .subImm .x .x3 .x3 1]

end VG.Impl.Ed25519.AArch64
