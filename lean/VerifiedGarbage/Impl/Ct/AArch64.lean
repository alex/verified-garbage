import VerifiedGarbage.TCB.AArch64.Isa

/-! Constant-time byte comparison on baseline AArch64. -/
namespace VG.Impl.Ct.AArch64
open VG.AArch64

def step : List Instr := [
  .add .x .x5 .x0 .x8, .ldrb .x6 .x5 0,
  .add .x .x5 .x2 .x8, .ldrb .x7 .x5 0,
  .logic .eor .x .x6 .x6 .x7, .logic .orr .x .x4 .x4 .x6,
  .addImm .x .x8 .x8 1, .sub .x .x9 .x8 .x1]

def finish : Prog isa := .block [.subImm .x .x4 .x4 1, .lsr .x .x0 .x4 63]

def equal : Prog isa :=
  .seq (.block [.movz .x .x8 0 0])
    (.seq (.ite (.zero .x .x1) (.block []) (.loop (.block step) (.nonzero .x .x9))) finish)

def eq : Prog isa :=
  .seq (.block [.movz .x .x4 0 0, .sub .x .x9 .x1 .x3])
    (.ite (.zero .x .x9) equal (.block [.movz .w .x0 0 0]))
end VG.Impl.Ct.AArch64
