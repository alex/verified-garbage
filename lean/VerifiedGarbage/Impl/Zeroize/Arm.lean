import VerifiedGarbage.TCB.Arm.Isa

/-! Eight four-byte stores (32 bytes) at a time, then four-byte stores, then
a byte tail. -/
namespace VG.Impl.Zeroize.Arm
open VG.Arm

def step (word : Bool) : List Instr :=
  [if word then .str .r2 .r0 0 else .strb .r2 .r0 0,
   .dp .add .r0 .r0 (.imm (if word then 4 else 1)), .subs .r3 .r3 (.imm 1)]

/-- Eight words, at `r0`, `r0 + 4`, …, `r0 + 28`. -/
def wideStep : List Instr :=
  [.str .r2 .r0 0, .str .r2 .r0 4, .str .r2 .r0 8, .str .r2 .r0 12,
   .str .r2 .r0 16, .str .r2 .r0 20, .str .r2 .r0 24, .str .r2 .r0 28,
   .dp .add .r0 .r0 (.imm 32), .subs .r3 .r3 (.imm 1)]

/-- `body` `r3` times. -/
def loopOf (body : List Instr) : Prog isa :=
  .seq (.block [.cmp .r3 (.imm 0)])
    (.ite .eq (.block []) (.loop (.block body) .ne))

def loop (word : Bool) : Prog isa := loopOf (step word)

def zeroize : Prog isa :=
  .seq (.block [.mov .r2 (.imm 0), .mov .r3 (.shifted .r1 .lsr 5)])
    (.seq (loopOf wideStep)
    (.seq (.block [.mov .r3 (.shifted .r1 .lsr 2), .dp .and .r3 .r3 (.imm 7)])
    (.seq (loop true) (.seq (.block [.dp .and .r1 .r1 (.imm 3), .mov .r3 (.reg .r1)]) (loop false)))))
end VG.Impl.Zeroize.Arm
