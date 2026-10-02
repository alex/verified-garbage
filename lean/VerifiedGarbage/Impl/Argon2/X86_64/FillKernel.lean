import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceMap
import VerifiedGarbage.Impl.Argon2.X86_64.FillPointers
import VerifiedGarbage.Impl.Argon2.X86_64.FillCompress

/-! Map the random word, prepare matrix pointers, and update one active cell.
The enclosing loops provide the position in callee-saved registers and the
frame; `rdi` contains either the cached independent word or the previous cell's
first word. The lane count and matrix base are reloaded after volatile calls.
-/

namespace VG.Impl.Argon2.X86_64.FillKernel

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def lanes : List Instr := [.mov .rsi (.mem (at_ .rbp 184))]
def matrix : List Instr := [.mov .r8 (.mem (at_ .rbp 232))]

def mapping : Prog isa := .seq (.block lanes) ReferenceMap.code

def pointers : Prog isa := .seq (.block matrix) FillPointers.code

def prepare : Prog isa := .seq mapping pointers

def code : Prog isa := .seq prepare FillCompress.code

end VG.Impl.Argon2.X86_64.FillKernel
