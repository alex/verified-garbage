import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Common

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_add` and `vg_mldsa_sub`

`add(f = r0, g = r1)` and `sub(f = r0, g = r1)`: a loop over the 256
coefficients, `r0` and `r1` pointing at coefficient `i` of `f` and `g`, and
`r2 = 256 - i` counting down with `subs`. They use only `r0`–`r3` and `r12`,
so they save nothing and use no stack, and `q` is not in a register: `- q`
is three subtractions and additions of immediates (`subQ`, as
`q = 2²³ - 2¹³ + 1`), and `+ q` if negative is `fixupS`, with the mask
`c = u >> 31` shifted instead of multiplied. A sum `a + b` is reduced as
`fixupS (a + b - q)`, a difference as `fixupS (a - b)`. Every address and
branch depends only on the pointers.
-/

namespace VG.Impl.MlDsa.Arm.Arith

open VG.Arm

/-- `r ← r - q`. -/
def subQ (r : Reg) : List Instr :=
  [.dp .sub r r (.imm 0x800000), .dp .add r r (.imm 0x2000), .dp .sub r r (.imm 1)]

/-- `r ← r + q` if `r` is negative, with `t` as a temporary:
`c · q = (c << 23) - (c << 13) + c` for `c = r >> 31`. -/
def fixupS (r t : Reg) : List Instr :=
  [.mov t (.shifted r .lsr 31), .dp .add r r (.shifted t .lsl 23), .dp .sub r r (.shifted t .lsl 13),
   .dp .add r r (.reg t)]

/-- The end of an iteration: store, advance, count down. -/
def accTail : List Instr :=
  [.str .r3 .r0 0, .dp .add .r0 .r0 (.imm 4), .dp .add .r1 .r1 (.imm 4), .subs .r2 .r2 (.imm 1)]

def addBody : List Instr :=
  [.ldr .r3 .r0 0, .ldr .r12 .r1 0, .dp .add .r3 .r3 (.reg .r12)] ++ subQ .r3 ++ fixupS .r3 .r12 ++
    accTail

def subBody : List Instr :=
  [.ldr .r3 .r0 0, .ldr .r12 .r1 0, .dp .sub .r3 .r3 (.reg .r12)] ++ fixupS .r3 .r12 ++ accTail

def add : Prog isa := .seq (.block [.mov .r2 (.imm 256)]) (.loop (.block addBody) .ne)

def sub : Prog isa := .seq (.block [.mov .r2 (.imm 256)]) (.loop (.block subBody) .ne)

end VG.Impl.MlDsa.Arm.Arith
