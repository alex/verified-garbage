import VerifiedGarbage.Impl.Argon2.X86_64.Compress

/-! Clear one 1024-byte address-generation block. The destination in `rdi`
is public; neither the old contents nor any input value affects the trace.
-/

namespace VG.Impl.Argon2.X86_64.ClearBlock

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def word (i : Nat) : List Instr := [.store (at_ .rdi (8 * i)) .rax]

def words (n : Nat) : List Instr := (List.range n).flatMap word

def code : Prog isa := .seq (.block [.mov .rax (.imm 0)]) (.block (words 128))

end VG.Impl.Argon2.X86_64.ClearBlock
