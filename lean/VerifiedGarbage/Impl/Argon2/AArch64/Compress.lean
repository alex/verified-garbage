import VerifiedGarbage.Spec.Argon2
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Argon2 compression G on ARM64

Baseline integer instructions; no additional CPU feature is required. Inputs
are x0 and x1, output x2, scratch x3. Scratch holds R at offset 0 and its
permuted copy at offset 1024. GB uses x4-x7, with x8-x10 as temporaries.
Every address is a public pointer plus a fixed offset; there are no branches,
calls, stack accesses, or writes to callee-saved or vector registers.
-/

namespace VG.Impl.Argon2.AArch64

open VG.AArch64

/-- BlaMka addition: zero-extend both low halves before the 64-bit product. -/
def addMul (a b : Reg) : List Instr := [
  .logic .orr .w .x8 a a, .logic .orr .w .x10 b b, .mul .x .x8 .x8 .x10,
  .add .x a a b, .add .x a a .x8, .add .x a a .x8]

/-- Half of GB, parameterized by its two rotation counts. -/
def halfGB (r1 r2 : Nat) : List Instr :=
  addMul .x4 .x5 ++
  ([.logic .eor .x .x7 .x7 .x4, .ror .x .x7 .x7 r1] : List Instr) ++
  addMul .x6 .x7 ++
  ([.logic .eor .x .x5 .x5 .x6, .ror .x .x5 .x5 r2] : List Instr)

/-- GB, on the four caller-saved registers x4–x7. -/
def gb : List Instr := halfGB 32 24 ++ halfGB 16 63

/-- GB on words `a,b,c,d` of the permuted scratch block. -/
def gbAt (a b c d : Nat) : Prog isa :=
  .seq (.block [
    .ldr .x .x4 .x3 (1024 + 8 * a),
    .ldr .x .x5 .x3 (1024 + 8 * b),
    .ldr .x .x6 .x3 (1024 + 8 * c),
    .ldr .x .x7 .x3 (1024 + 8 * d)]) <|
  .seq (.block gb) (.block [
    .str .x .x4 .x3 (1024 + 8 * a),
    .str .x .x5 .x3 (1024 + 8 * b),
    .str .x .x6 .x3 (1024 + 8 * c),
    .str .x .x7 .x3 (1024 + 8 * d)])

/-- P over a row or column selected by `index`. -/
def permuteAt (index : Fin 16 → Fin 128) : Prog isa :=
  let step (a b c d : Fin 16) := gbAt (index a).val (index b).val (index c).val (index d).val
  .seq (step 0 4 8 12) <| .seq (step 1 5 9 13) <|
  .seq (step 2 6 10 14) <| .seq (step 3 7 11 15) <|
  .seq (step 0 5 10 15) <| .seq (step 1 6 11 12) <|
  .seq (step 2 7 8 13) (step 3 4 9 14)

/-- Copy one word of X XOR Y into both scratch blocks. -/
def initWord (i : Nat) : List Instr := [
  .ldr .x .x8 .x0 (8 * i), .ldr .x .x9 .x1 (8 * i),
  .logic .eor .x .x8 .x8 .x9,
  .str .x .x8 .x3 (8 * i), .str .x .x8 .x3 (1024 + 8 * i)]

/-- XOR the original R into the permuted word and write the output. -/
def finishWord (i : Nat) : List Instr := [
  .ldr .x .x8 .x3 (1024 + 8 * i), .ldr .x .x9 .x3 (8 * i),
  .logic .eor .x .x8 .x8 .x9, .str .x .x8 .x2 (8 * i)]

/-- The complete compression function. The input pointers are `x0,x1`,
the output pointer is `x2`, and scratch is `x3`. -/
def compress : Prog isa :=
  .seq (.block ((List.range 128).flatMap initWord)) <|
  .seq ((List.finRange 8).foldr (fun row rest =>
    .seq (permuteAt (Spec.Argon2.rowIndex row)) rest) (.block [])) <|
  .seq ((List.finRange 8).foldr (fun col rest =>
    .seq (permuteAt (Spec.Argon2.colIndex col)) rest) (.block [])) <|
  .block ((List.range 128).flatMap finishWord)

end VG.Impl.Argon2.AArch64
