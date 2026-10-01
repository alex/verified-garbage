import VerifiedGarbage.Impl.Ed25519.X86_64.PointSelect
import VerifiedGarbage.Impl.Ed25519.X86_64.PointTable

/-! A descending scalar bit: add its point power, then select using the bit mask. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

/-- rbx selects the local power; rsi is the public bit offset of the batch. -/
def scalarBitMask : List Instr :=
  [.mov .rax (.reg .rbx), .alu .add .rax (.reg .rsi),
    .movzx8 .rcx { base := .rdi, index := some .rax, disp := 768 }, .alu .sub .rcx (.imm 1)]

def prepareAdd (fld : Arith) : List Instr :=
  savePoint fld ++ tableAddr 5376 ++ pointFromTable ++ copyPointToQ fld ++ (restorePoint fld)

def pointAccumulate (fld : Arith) : List Instr :=
  prepareAdd fld ++ pointAdd fld ++ scalarBitMask ++ pointSelect

end VG.Impl.Ed25519.X86_64
