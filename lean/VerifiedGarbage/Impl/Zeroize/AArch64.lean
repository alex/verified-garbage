import VerifiedGarbage.TCB.AArch64.Isa

/-! Word stores followed by a byte tail. Normal-memory stores may be unaligned. -/
namespace VG.Impl.Zeroize.AArch64
open VG.AArch64

def step (word : Bool) : List Instr :=
  [if word then .str .x .x2 .x0 0 else .strb .x2 .x0 0,
   .addImm .x .x0 .x0 (if word then 8 else 1), .subImm .x .x3 .x3 1]

def loop (word : Bool) : Prog isa :=
  .ite (.zero .x .x3) (.block []) (.loop (.block (step word)) (.nonzero .x .x3))

def zeroize : Prog isa :=
  .seq (.block [.movz .x .x2 0 0, .lsr .x .x3 .x1 3, .movz .x .x4 7 0,
    .logic .and .x .x1 .x1 .x4])
    (.seq (loop true) (.seq (.block [.addImm .x .x3 .x1 0]) (loop false)))
end VG.Impl.Zeroize.AArch64
