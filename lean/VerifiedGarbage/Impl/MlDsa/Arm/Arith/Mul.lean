import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Common

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

`multiplyNTT(h = r0, f = r1, g = r2)` and `multiplyAddNTT(h = r0, f = r1,
g = r2)` save `r4`–`r9` (`saving`: 24 bytes of stack), put `q` in `r4`, and
run over the 256 coefficients with `r0`, `r1` and `r2` pointing at
coefficient `i` of `h`, `f` and `g`, and `r3 = 256 - i` counting down: the
pieces of `f[i]` go to `r5`–`r7`, and `mulz` multiplies `g[i]` (in `r8`) by
them, into `r9`, less than `2q`; `csub` reduces it (for `multiplyAddNTT`,
`h[i]` is added and the sum reduced with `red` first, as it is less than
`2q + q < 2²⁵`). Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlDsa.Arm.Arith

open VG.Arm

/-- The registers the multiplications save. -/
def mulSaved : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9]

/-- Advance the three pointers and count down. -/
def step3 : List Instr :=
  [.dp .add .r0 .r0 (.imm 4), .dp .add .r1 .r1 (.imm 4), .dp .add .r2 .r2 (.imm 4), .subs .r3 .r3 (.imm 1)]

/-- `f[i] · g[i]` modulo `q`, less than `2q`, in `r9`. -/
def mulHead : List Instr := [.ldr .r12 .r1 0] ++ zPieces .r12 ++ [.ldr .r8 .r2 0] ++ mulz .r9 .r8 .r12

def mulBody : List Instr := mulHead ++ csub .r9 .r12 .r4 ++ [.str .r9 .r0 0] ++ step3

def mulAddBody : List Instr :=
  mulHead ++ [.ldr .r8 .r0 0, .dp .add .r9 .r9 (.reg .r8)] ++ red .r9 .r12 .r4 ++ csub .r9 .r12 .r4 ++
    [.str .r9 .r0 0] ++ step3

def mul : Prog isa :=
  saving mulSaved (.seq (.block (loadQ .r4 ++ [.mov .r3 (.imm 256)])) (.loop (.block mulBody) .ne))

def mulAdd : Prog isa :=
  saving mulSaved (.seq (.block (loadQ .r4 ++ [.mov .r3 (.imm 256)])) (.loop (.block mulAddBody) .ne))

end VG.Impl.MlDsa.Arm.Arith
