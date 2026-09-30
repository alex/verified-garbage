import VerifiedGarbage.Impl.Ed25519.X86.InputBits

namespace VG.Impl.Ed25519.X86
open VG.X86 VG.Impl.X25519.X86

def loadSlicePointer (i skip : Nat) : List Instr :=
  [.mov .esi (.mem (at_ .esp (4 + 4 * i))), .alu .add .esi (.imm (BitVec.ofNat 32 skip))]
def inputSliceWords (i skip dst n : Nat) : List Instr := loadSlicePointer i skip ++ copyWords dst n
def inputSliceBits (i skip bytes : Nat) : List Instr := loadSlicePointer i skip ++ expandScalarBits bytes

end VG.Impl.Ed25519.X86
