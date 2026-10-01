import VerifiedGarbage.Impl.Ed25519.X86_64.PointAccumulate

/-! Consume sixteen scalar bits, descending through a local table of powers. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

def accumulateBody (fld : Arith) : List Instr :=
  ([.alu .sub .rbx (.imm 1)] : List Instr) ++ pointAccumulate fld ++ [.alu .test .rbx (.reg .rbx)]

def accumulate16 (fld : Arith) : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 16)]) (.loop (.block (accumulateBody fld)) .ne)

end VG.Impl.Ed25519.X86_64
