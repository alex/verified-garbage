import VerifiedGarbage.Impl.Ed25519.Arm.RecoverSign
import VerifiedGarbage.Impl.Ed25519.Arm.Packed

/-! Strict point decoding through r12. Sign metadata lives outside field scratch. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def splitYSign : List Instr :=
  [.ldr .r3 .r0 (offset 1 + 60), .mov .r2 (.shifted .r3 .lsr 15), .str .r2 .r0 60,
    .movw .r4 32767, .dp .and .r3 .r3 (.reg .r4), .str .r3 .r0 (offset 1 + 60)]

def canonicalY : Prog isa := .seq (.block (freeze 1)) (.block (wordsEqual (offset 1) FR))

def pointDecodeLoad : Prog isa :=
  .seq (.block (unpackField (offset 1) 0 ++ splitYSign)) canonicalY

def pointDecode : Prog isa := .seq pointDecodeLoad (.ite .eq recoverPoint recoverInvalid)

end VG.Impl.Ed25519.Arm
