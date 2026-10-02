import VerifiedGarbage.Impl.Argon2.X86_64.Compress

/-! Write the compression result into the current matrix block. `rsi` points
to the temporary result and `rdi` to the matrix destination; `r9` is the public
pass number. Pass zero copies the result, and later passes XOR the old cell.
Both paths visit every word in ascending order.
-/

namespace VG.Impl.Argon2.X86_64.FillWrite

open VG.X86_64
open VG.Impl.Argon2.X86_64 (at_)

def word (xorOld : Bool) (i : Nat) : List Instr :=
  [.mov .rax (.mem (at_ .rsi (8 * i)))] ++
    (if xorOld then [.alu .xor .rax (.mem (at_ .rdi (8 * i)))] else []) ++
    [.store (at_ .rdi (8 * i)) .rax]

def words (xorOld : Bool) (n : Nat) : List Instr := (List.range n).flatMap (word xorOld)

def code : Prog isa := .seq (.block [.alu .cmp .r9 (.imm 0)])
  (.ite .e (.block (words false 128)) (.block (words true 128)))

end VG.Impl.Argon2.X86_64.FillWrite
