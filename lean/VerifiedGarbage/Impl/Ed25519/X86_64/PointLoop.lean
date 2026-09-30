import VerifiedGarbage.Impl.Ed25519.X86_64.FieldMemory

/-! Fixed batches of doubling, with a public counter in rsi. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

def doubleBody : List Instr := pointDouble ++ [.alu .sub .rsi (.imm 1)]

def double16 : Prog isa :=
  .seq (.block [.mov32 .rsi (.imm 16)]) (.loop (.block doubleBody) .ne)

end VG.Impl.Ed25519.X86_64
