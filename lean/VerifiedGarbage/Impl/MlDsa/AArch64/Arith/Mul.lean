import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common

/-!
# ML-DSA on AArch64: `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

`multiplyNTT(h = x0, f = x1, g = x2)` and `multiplyAddNTT(h = x0, f = x1,
g = x2)` run over the 256 coefficients with `x0`, `x1` and `x2` pointing at
coefficient `i` of `h`, `f` and `g`, and `x12 = 256 - i` counting down: the
product `f[i] · g[i]` (by `mul`, less than `q²`; for `multiplyAddNTT`, plus
`h[i]`, still less than `q²`) is reduced with `reduce` and stored to `h[i]`.
Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlDsa.AArch64.Arith

open VG.AArch64

/-- Advance the three pointers and count down. -/
def step3 : List Instr :=
  [.addImm .x .x0 .x0 4, .addImm .x .x1 .x1 4, .addImm .x .x2 .x2 4, .subImm .x .x12 .x12 1]

/-- `f[i] · g[i]`, in `x13`. -/
def mulHead : List Instr := [.ldr .w .x13 .x1 0, .ldr .w .x14 .x2 0, .mul .x .x13 .x13 .x14]

/-- `f[i] · g[i] + h[i]`, in `x13`. -/
def mulAddHead : List Instr := mulHead ++ [.ldr .w .x14 .x0 0, .add .x .x13 .x13 .x14]

def mulBody : List Instr := mulHead ++ reduce .x13 .x14 ++ [.str .w .x13 .x0 0] ++ step3

def mulAddBody : List Instr := mulAddHead ++ reduce .x13 .x14 ++ [.str .w .x13 .x0 0] ++ step3

/-- The constants, and 256 in `x12`. -/
def mulPro : List Instr := consts ++ [.movz .x .x12 256 0]

def mul : Prog isa := .seq (.block mulPro) (.loop (.block mulBody) (.nonzero .x .x12))

def mulAdd : Prog isa := .seq (.block mulPro) (.loop (.block mulAddBody) (.nonzero .x .x12))

end VG.Impl.MlDsa.AArch64.Arith
