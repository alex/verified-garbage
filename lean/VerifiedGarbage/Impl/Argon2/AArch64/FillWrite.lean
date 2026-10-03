import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.Compress

/-! Write the compression result into the current matrix block. `x1` points
to the temporary result and `x0` to the matrix destination; `x5` is the public
pass number. Pass zero copies the result, and later passes XOR the old cell.
Both paths visit every word in ascending order.
-/

namespace VG.Impl.Argon2.AArch64.FillWrite

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def word (xorOld : Bool) (i : Nat) : List Instr :=
  [load .x8 .x1 (8 * i)].flatten ++
    (if xorOld then [xorm .x8 .x0 (8 * i)].flatten else []) ++
    [store .x0 (8 * i) .x8].flatten

def words (xorOld : Bool) (n : Nat) : List Instr := (List.range n).flatMap (word xorOld)

def code : Prog isa := .seq (.block [comparei .x5 0].flatten)
  (.ite (.zero .x .x15) (.block (words false 128)) (.block (words true 128)))

end VG.Impl.Argon2.AArch64.FillWrite
