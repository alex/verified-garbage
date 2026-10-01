import VerifiedGarbage.Impl.Ed25519.X86.PointSelect
import VerifiedGarbage.Impl.Ed25519.X86.PointTable

/-! A descending scalar bit adds its exact power before masked selection. -/
namespace VG.Impl.Ed25519.X86
open VG.X86
open VG.Impl.X25519.X86 (sc at_)

def scalarBitMask : List Instr :=
  [.mov .eax (.mem (sc 28)), .mov .edx (.imm 16), .mul .edx,
    .alu .add .eax (.reg .esi), .alu .add .eax (.reg .edi),
    .movzx8 .ecx (at_ .eax 7168), .alu .sub .ecx (.imm 1)]

def prepareAdd : List Instr :=
  savePoint ++ tableAddr 5120 ++ pointFromTable ++ copyPointToQ ++ restorePoint

def pointAccumulate : List Instr := prepareAdd ++ pointAdd ++ scalarBitMask ++ pointSelect

def accumulateBody : List Instr :=
  [.alu .sub .esi (.imm 1)] ++ pointAccumulate ++ [.alu .test .esi (.reg .esi)]

def accumulate16 : Prog isa :=
  .seq (.block [.mov .esi (.imm 16)]) (.loop (.block accumulateBody) .ne)

end VG.Impl.Ed25519.X86
