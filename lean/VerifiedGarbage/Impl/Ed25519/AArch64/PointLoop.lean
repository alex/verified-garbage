import VerifiedGarbage.Impl.Ed25519.AArch64.FieldMemory

/-! A doubling, counting down a public counter in x1. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def doubleBody : List Instr := pointDouble ++ [.subImm .x .x1 .x1 1]

end VG.Impl.Ed25519.AArch64
