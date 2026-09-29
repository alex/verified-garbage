import VerifiedGarbage.TCB.AArch64.Isa

/-!
# ML-KEM on AArch64: helpers, `vg_mlkem_add` and `vg_mlkem_sub`

Coefficients are `u32`s less than `q = 3329`, loaded with `ldr w` (which
zero-extends them) and computed on in 64-bit registers, where no
intermediate value wraps. A value less than `2q` is reduced with one
conditional subtraction without a branch (`csub`): `d - q` is negative
exactly when `d < q`, which its sign bit (bit 63) says, and `madd` adds `q`
back times that bit. The model has no flags, conditional select or
register-offset addressing: pointers advance by an immediate, and loops
count down to zero (`cbnz`).

* `add(f = x0, g = x1)`: `f[i] ← (f[i] + g[i]) mod q`.
* `sub(f = x0, g = x1)`: `f[i] ← (f[i] + q - g[i]) mod q`.

Both are the same loop (`mapLoop`), around the arithmetic `addOp` or
`subOp` of `x11 = f[i]` and `x12 = g[i]`, with `x9 = q` and `x10` the
coefficients left. Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

/-- `mov d, n` (`add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- `d ← d mod q` for `d < 2q`, with `q` in `qr` and a temporary `t`:
`d - q`, plus `q` if that is negative. -/
def csub (d t qr : Reg) : List Instr := [.sub .x d d qr, .lsr .x t d 63, .madd .x d t qr d]

/-- `x11 ← (x11 + x12) mod q`. -/
def addOp : List Instr := (.add .x .x11 .x11 .x12 :: csub .x11 .x13 .x9 : List Instr)

/-- `x11 ← (x11 + q - x12) mod q`. -/
def subOp : List Instr :=
  (.add .x .x11 .x11 .x9 :: .sub .x .x11 .x11 .x12 :: csub .x11 .x13 .x9 : List Instr)

/-- One coefficient: `x11 = f[i]`, `x12 = g[i]`, `op`, `f[i] ← x11`, and on to
the next. -/
def mapBody (op : List Instr) : List Instr :=
  [.ldr .w .x11 .x0 0, .ldr .w .x12 .x1 0] ++ op ++
    ([.str .w .x11 .x0 0, .addImm .x .x0 .x0 4, .addImm .x .x1 .x1 4, .subImm .x .x10 .x10 1] :
      List Instr)

/-- `op` on each of the 256 coefficients. -/
def mapLoop (op : List Instr) : Prog isa :=
  .seq (.block [.movz .x .x9 3329 0, .movz .x .x10 256 0]) (.loop (.block (mapBody op)) (.nonzero .x .x10))

def add : Prog isa := mapLoop addOp

def sub : Prog isa := mapLoop subOp

end VG.Impl.MlKem.AArch64
