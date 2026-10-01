import VerifiedGarbage.Impl.Ed25519.X86.FieldMemory

/-! Sixteen doublings with a public register counter. -/
namespace VG.Impl.Ed25519.X86
open VG.X86

def doubleBody : List Instr := pointDouble ++ [.alu .sub .esi (.imm 1)]
def double16 : Prog isa :=
  .seq (.block [.mov .esi (.imm 16)]) (.loop (.block doubleBody) .ne)

end VG.Impl.Ed25519.X86
