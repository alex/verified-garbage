import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.Compress

/-! Clear one 1024-byte address-generation block. The destination in `x0`
is public; neither the old contents nor any input value affects the trace.
-/

namespace VG.Impl.Argon2.AArch64.ClearBlock

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def word (i : Nat) : List Instr := [store .x0 (8 * i) .x8].flatten

def words (n : Nat) : List Instr := (List.range n).flatMap word

def code : Prog isa := .seq (.block [imm .x8 0].flatten) (.block (words 128))

end VG.Impl.Argon2.AArch64.ClearBlock
