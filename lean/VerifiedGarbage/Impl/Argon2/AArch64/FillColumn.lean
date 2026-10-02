import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.TCB.AArch64.Isa

/-! Current and preceding columns in the filling loop. The public slice,
segment length and offset are in `x22`, `x21` and `x23`, and the lane length
is in `x20`. `x3` receives the current column; `x0` receives its cyclic
predecessor. Only the public column-zero test controls a branch.
-/

namespace VG.Impl.Argon2.AArch64.FillColumn

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def current : List Instr := [mov .x8 .x22, mul .x21, mov .x3 .x8, add .x3 .x23].flatten

def select : Prog isa := .ite (.zero .x .x15)
  (.block [mov .x0 .x20].flatten) (.block [mov .x0 .x3].flatten)

def previous : Prog isa :=
  .seq (.block [comparei .x3 0].flatten)
    (.seq select (.block [subi .x0 1].flatten))

def code : Prog isa := .seq (.block current) previous

end VG.Impl.Argon2.AArch64.FillColumn
