import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Impl.Argon2.AArch64.ReferenceMap
import VerifiedGarbage.Impl.Argon2.AArch64.FillPointers
import VerifiedGarbage.Impl.Argon2.AArch64.FillCompress

/-! Map the random word, prepare matrix pointers, and update one active cell.
The enclosing loops provide the position in callee-saved registers and the
frame; `x0` contains either the cached independent word or the previous cell's
first word. The lane count and matrix base are reloaded after volatile calls.
-/

namespace VG.Impl.Argon2.AArch64.FillKernel

open VG.AArch64
open VG.Impl.Argon2.AArch64.Instructions

def lanes : List Instr := [load .x1 .x19 184].flatten
def matrix : List Instr := [load .x4 .x19 232].flatten

def mapping : Prog isa := .seq (.block lanes) ReferenceMap.code

def pointers : Prog isa := .seq (.block matrix) FillPointers.code

def prepare : Prog isa := .seq mapping pointers

def code : Prog isa := .seq prepare FillCompress.code

end VG.Impl.Argon2.AArch64.FillKernel
