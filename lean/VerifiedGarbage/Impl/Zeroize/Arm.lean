import VerifiedGarbage.TCB.Arm.Isa

/-! Four-byte stores followed by a byte tail. -/
namespace VG.Impl.Zeroize.Arm
open VG.Arm

def step (word : Bool) : List Instr :=
  [if word then .str .r2 .r0 0 else .strb .r2 .r0 0,
   .dp .add .r0 .r0 (.imm (if word then 4 else 1)), .subs .r3 .r3 (.imm 1)]

def loop (word : Bool) : Prog isa :=
  .seq (.block [.cmp .r3 (.imm 0)])
    (.ite .eq (.block []) (.loop (.block (step word)) .ne))

def zeroize : Prog isa :=
  .seq (.block [.mov .r2 (.imm 0), .mov .r3 (.shifted .r1 .lsr 2), .dp .and .r1 .r1 (.imm 3)])
    (.seq (loop true) (.seq (.block [.mov .r3 (.reg .r1)]) (loop false)))
end VG.Impl.Zeroize.Arm
