import VerifiedGarbage.Impl.Ed25519.X86_64.RecoverSign

/-! Decode a canonical 32-byte Ed25519 point. The input pointer is in rdx. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (at_ low63 loadU store4)

def loadSign : List Instr := [.mov .rsi (.mem (at_ .rdx 24)), .shift .shr .rsi 63]

/-- Add 19 to a 255-bit y. Its high bit is set precisely for y >= p. -/
def canonicalY : List Instr :=
  [.movImm64 .rdx low63,
    .mov .r12 (.reg .r8), .alu .add .r12 (.imm 19), .mov .r13 (.reg .r9), .alu .adc .r13 (.imm 0),
    .mov .r14 (.reg .r10), .alu .adc .r14 (.imm 0), .mov .r15 (.reg .r11), .alu .adc .r15 (.imm 0),
    .mov .rax (.reg .r15), .shift .shr .rax 63, .alu .and .r15 (.reg .rdx),
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax), .alu .test .rcx (.reg .rcx)]

def pointDecodeLoad : List Instr := loadSign ++ loadU ++ store4 (offset 1) ++ canonicalY

def pointDecode (fld : Arith) : Prog isa :=
  .seq (.block pointDecodeLoad) (.ite .e (recoverPoint fld) recoverInvalid)

end VG.Impl.Ed25519.X86_64
