import VerifiedGarbage.Impl.Ed25519.AArch64.FieldMemory

/-! Fixed batches of doubling, with a public counter in x1. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def doubleBody : List Instr := pointDouble ++ [.subImm .x .x1 .x1 1]

def double16 : Prog isa :=
  .seq (.block [.movz .w .x1 16 0]) (.loop (.block doubleBody) (.nonzero .x .x1))

end VG.Impl.Ed25519.AArch64
