import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Vec

/-!
# ML-DSA on x86-64: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

`multiplyNTT(h = rdi, f = rsi, g = rdx)` and `multiplyAddNTT(h = rdi,
f = rsi, g = rdx)` compute on four coefficients at a time, as doublewords of
SSE registers (see `Vec.lean`), with `rdi`, `rsi` and `rdx` pointing at
coefficient `4i` of `h`, `f` and `g`, and `rcx = 63 - i` counting down:
`vmont` of `f` by `g` is `f · g · 2⁻³²`, and `vmont` of that by
`2⁶⁴ mod q = 2365951` (in `xmm11`) is `f · g`, less than `2q`, which `vcsub`
reduces (for `multiplyAddNTT`, `h` is then added and the sum reduced), and
it is stored to `h`.

The functions have no working space and use no stack, so `withMxcsr` saves
MXCSR through the last 8 bytes of `h` (`r8 = h`): the last four coefficients
of `h` are loaded to `xmm6` first, the loop stores the first 252, the last
four are computed from registers before MXCSR is loaded back, and stored
after it. Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlDsa.X86_64.Arith

open VG.X86_64
open VG.Impl.MlKem.X86_64 (xb xmov withMxcsr rcxLoop)

/-- The constants and `2⁶⁴ mod q` in the doublewords of `xmm11`. -/
def mulPro : List Instr :=
  vconsts ++ [.mov32 .rax (.imm 2365951), .xop (.movq .xmm11 .rax), .xop (.pshufd .xmm11 .xmm11 0)]

/-- The coefficients of `f`, `g` and `h` to `xmm3`, `xmm13` and `xmm5`. -/
def mulLoads : List Instr :=
  [.movdquLoad .xmm3 (at_ .rsi 0), .movdquLoad .xmm13 (at_ .rdx 0), .movdquLoad .xmm5 (at_ .rdi 0)]

/-- `f · g` for four coefficients, in `[0, q)`, in `xmm3`. -/
def mulCore : List Instr :=
  [.xop (.pshufd .xmm12 .xmm13 0xF5)] ++ vmont .xmm3 .xmm13 .xmm12 .xmm2 .xmm4 ++
    vmont .xmm3 .xmm11 .xmm11 .xmm2 .xmm4 ++ vcsub .xmm3 .xmm2

/-- `h + f · g` for four coefficients, in `[0, q)`, in `xmm3`. -/
def mulAddCore : List Instr := mulCore ++ [xb .paddd .xmm3 .xmm5] ++ vcsub .xmm3 .xmm2

/-- Store `xmm3` to `h` and advance the three pointers. -/
def mulTail : List Instr :=
  [.movdquStore (at_ .rdi 0) .xmm3, .alu .add .rdi (.imm 16), .alu .add .rsi (.imm 16),
    .alu .add .rdx (.imm 16)]

/-- The last four coefficients, with those of `h` in `xmm6`, to `xmm3`. -/
def mulLast (core : List Instr) : List Instr :=
  [.movdquLoad .xmm3 (at_ .rsi 0), .movdquLoad .xmm13 (at_ .rdx 0), xmov .xmm5 .xmm6] ++ core

/-- A function of `h`, `f` and `g` four coefficients at a time by `core`. -/
def mulFn (core : List Instr) : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rdi), .movdquLoad .xmm6 (at_ .rdi 1008)])
    (.seq (withMxcsr .r8 1016
        (.seq (.block mulPro) (.seq (rcxLoop 63 (mulLoads ++ core ++ mulTail)) (.block (mulLast core)))))
      (.block [.movdquStore (at_ .rdi 0) .xmm3]))

def mul : Prog isa := mulFn mulCore

def mulAdd : Prog isa := mulFn mulAddCore

end VG.Impl.MlDsa.X86_64.Arith
