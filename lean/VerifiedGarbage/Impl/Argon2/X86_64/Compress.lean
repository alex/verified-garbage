import VerifiedGarbage.Spec.Argon2
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Argon2 compression G on x86-64

Baseline scalar instructions. The inputs and output are 1024-byte blocks;
`rcx` points to the 4096-byte scratch allocation. `[0,1024)` holds R = X XOR Y,
`[1024,2048)` holds the permuted copy. Once the inputs have been copied,
`rdi` holds the output pointer across multiplications (which overwrite `rdx`).
All other working registers are caller-saved. The four words of each GB
are loaded into `r8`–`r11` and stored back after it. Every address is a
public pointer plus a fixed offset, and the code has no branches.
-/

namespace VG.Impl.Argon2.X86_64

open VG.X86_64

def at_ (base : Reg) (offset : Nat) : MemOp := { base, disp := offset }

/-- Add with the doubled low-half product. `a` and `b` are distinct from
`rax`, `rdx` and `rsi`, which are temporaries. -/
def addMul (a b : Reg) : List Instr := [
  .mov32 .rax (.reg a), .mov32 .rsi (.reg b), .mul .rsi,
  .alu .add a (.reg b), .alu .add a (.reg .rax), .alu .add a (.reg .rax)]

/-- Half of GB, parameterized by its two rotation counts. -/
def halfGB (r1 r2 : Nat) : List Instr :=
  addMul .r8 .r9 ++
  ([.alu .xor .r11 (.reg .r8), .shift .ror .r11 r1] : List Instr) ++
  addMul .r10 .r11 ++
  ([.alu .xor .r9 (.reg .r10), .shift .ror .r9 r2] : List Instr)

/-- GB, on the four caller-saved registers r8–r11. -/
def gb : List Instr := halfGB 32 24 ++ halfGB 16 63

/-- GB on words `a,b,c,d` of the permuted scratch block. -/
def gbAt (a b c d : Nat) : Prog isa :=
  .seq (.block [
    .mov .r8 (.mem (at_ .rcx (1024 + 8 * a))),
    .mov .r9 (.mem (at_ .rcx (1024 + 8 * b))),
    .mov .r10 (.mem (at_ .rcx (1024 + 8 * c))),
    .mov .r11 (.mem (at_ .rcx (1024 + 8 * d)))]) <|
  .seq (.block gb) (.block [
    .store (at_ .rcx (1024 + 8 * a)) .r8,
    .store (at_ .rcx (1024 + 8 * b)) .r9,
    .store (at_ .rcx (1024 + 8 * c)) .r10,
    .store (at_ .rcx (1024 + 8 * d)) .r11])

/-- P over a row or column selected by `index`. -/
def permuteAt (index : Fin 16 → Fin 128) : Prog isa :=
  let step (a b c d : Fin 16) := gbAt (index a).val (index b).val (index c).val (index d).val
  .seq (step 0 4 8 12) <| .seq (step 1 5 9 13) <|
  .seq (step 2 6 10 14) <| .seq (step 3 7 11 15) <|
  .seq (step 0 5 10 15) <| .seq (step 1 6 11 12) <|
  .seq (step 2 7 8 13) (step 3 4 9 14)

/-- Copy one word of X XOR Y to both scratch blocks. -/
def initWord (i : Nat) : List Instr := [
  .mov .rax (.mem (at_ .rdi (8 * i))), .alu .xor .rax (.mem (at_ .rsi (8 * i))),
  .store (at_ .rcx (8 * i)) .rax, .store (at_ .rcx (1024 + 8 * i)) .rax]

/-- XOR the original R into one permuted word and write the output. -/
def finishWord (i : Nat) : List Instr := [
  .mov .rax (.mem (at_ .rcx (1024 + 8 * i))), .alu .xor .rax (.mem (at_ .rcx (8 * i))),
  .store (at_ .rdi (8 * i)) .rax]

/-- The complete compression function. The input pointers are `rdi,rsi`,
the output pointer is `rdx`, and scratch is `rcx`. -/
def compress : Prog isa :=
  .seq (.block ((List.range 128).flatMap initWord)) <|
  .seq (.block [.mov .rdi (.reg .rdx)]) <|
  .seq ((List.finRange 8).foldr (fun row rest =>
    .seq (permuteAt (Spec.Argon2.rowIndex row)) rest) (.block [])) <|
  .seq ((List.finRange 8).foldr (fun col rest =>
    .seq (permuteAt (Spec.Argon2.colIndex col)) rest) (.block [])) <|
  .block ((List.range 128).flatMap finishWord)

end VG.Impl.Argon2.X86_64
