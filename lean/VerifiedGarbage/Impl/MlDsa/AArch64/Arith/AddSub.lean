import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common

/-!
# ML-DSA on AArch64: `vg_mldsa_add` and `vg_mldsa_sub`

`add(f = x0, g = x1)` and `sub(f = x0, g = x1)` run over the 256
coefficients with `x0` and `x1` pointing at coefficient `i` of `f` and `g`,
and `x10 = 256 - i` counting down: `f[i] + g[i]` (for `sub`,
`f[i] + q - g[i]`), less than `2q`, is reduced with `csub` and stored to
`f[i]`. `q` is in `x9`. Every address and branch depends only on the
pointers.
-/

namespace VG.Impl.MlDsa.AArch64.Arith

open VG.AArch64
open VG.Impl.MlKem.AArch64 (csub)

/-- Advance the two pointers and count down. -/
def step2 : List Instr := [.addImm .x .x0 .x0 4, .addImm .x .x1 .x1 4, .subImm .x .x10 .x10 1]

def addBody : List Instr :=
  [.ldr .w .x11 .x0 0, .ldr .w .x12 .x1 0, .add .x .x11 .x11 .x12] ++ csub .x11 .x12 .x9 ++
    [.str .w .x11 .x0 0] ++ step2

def subBody : List Instr :=
  [.ldr .w .x11 .x0 0, .ldr .w .x12 .x1 0, .add .x .x11 .x11 .x9, .sub .x .x11 .x11 .x12] ++
    csub .x11 .x12 .x9 ++ [.str .w .x11 .x0 0] ++ step2

/-- `q` in `x9`, and 256 in `x10`. -/
def accPro : List Instr := movW .x9 (BitVec.ofNat 32 qNat) ++ [.movz .x .x10 256 0]

def add : Prog isa := .seq (.block accPro) (.loop (.block addBody) (.nonzero .x .x10))

def sub : Prog isa := .seq (.block accPro) (.loop (.block subBody) (.nonzero .x .x10))

end VG.Impl.MlDsa.AArch64.Arith
