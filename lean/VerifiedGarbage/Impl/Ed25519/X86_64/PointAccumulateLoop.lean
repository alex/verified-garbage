import VerifiedGarbage.Impl.Ed25519.X86_64.PointAccumulate

/-! Consume sixteen scalar bits, descending through a local table of powers. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64

def accumulateBody : List Instr :=
  ([.alu .sub .rbx (.imm 1)] : List Instr) ++ pointAccumulate ++ [.alu .test .rbx (.reg .rbx)]

def accumulate16 : Prog isa :=
  .seq (.block [.mov32 .rbx (.imm 16)]) (.loop (.block accumulateBody) .ne)

end VG.Impl.Ed25519.X86_64
