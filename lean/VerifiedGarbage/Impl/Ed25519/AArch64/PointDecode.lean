import VerifiedGarbage.Impl.Ed25519.AArch64.RecoverSign

/-! Decode a canonical point through the public input pointer x2. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def loadSign : List Instr := [.ldr .x .x1 .x2 24, .lsr .x .x1 .x1 63]

def loadY : List Instr :=
  [.ldr .x .x4 .x2 0, .ldr .x .x5 .x2 8, .ldr .x .x6 .x2 16, .ldr .x .x7 .x2 24] ++
    const64 .x8 low63 ++ [.logic .and .x .x7 .x7 .x8]

/-- For a 255-bit y, adding 19 sets bit 255 precisely when y >= p. -/
def canonicalY : List Instr :=
  [.movz .w .x10 0 0, .movz .w .x11 19 0,
    .adds .x .x21 .x4 .x11, .adcs .x .x22 .x5 .x10,
    .adcs .x .x23 .x6 .x10, .adcs .x .x24 .x7 .x10, .lsr .x .x8 .x24 63]

def pointDecodeLoad : List Instr := loadSign ++ loadY ++ store4 (offset 1) ++ canonicalY

def pointDecode : Prog isa :=
  .seq (.block pointDecodeLoad) (.ite (.zero .x .x8) recoverPoint recoverInvalid)

end VG.Impl.Ed25519.AArch64
