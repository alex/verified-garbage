import VerifiedGarbage.Impl.Ed25519.AArch64.PointAccumulate

/-! Descend through the sixteen scalar bits of a batch. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def accumulateBody : List Instr := ([.subImm .x .x19 .x19 1] : List Instr) ++ pointAccumulate

def accumulate16 : Prog isa :=
  .seq (.block [.movz .w .x19 16 0]) (.loop (.block accumulateBody) (.nonzero .x .x19))

end VG.Impl.Ed25519.AArch64
