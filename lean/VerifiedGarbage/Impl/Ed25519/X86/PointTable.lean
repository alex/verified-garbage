import VerifiedGarbage.Impl.Ed25519.X86.FieldMemory

/-! Point tables use eight little-endian words per coordinate. -/
namespace VG.Impl.Ed25519.X86
open VG.X86
open VG.Impl.X25519.X86 (at_)

def workspaceCopyWord (src dst : Reg) (a o k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ src (a + 4 * k))), .store (at_ dst (o + 4 * k)) .eax]

def workspaceCopyWords (src dst : Reg) (a o n : Nat) : List Instr :=
  (List.range n).flatMap (workspaceCopyWord src dst a o)

def pointToTable : List Instr := workspaceCopyWords .edi .edx 64 0 32
def pointFromTable : List Instr := workspaceCopyWords .edx .edi 0 64 32

def tableAddr (off : Nat) : List Instr :=
  [.mov .eax (.reg .esi), .mov .edx (.imm 128), .mul .edx,
    .alu .add .eax (.reg .edi), .alu .add .eax (.imm (BitVec.ofNat 32 off)),
    .mov .edx (.reg .eax)]

end VG.Impl.Ed25519.X86
