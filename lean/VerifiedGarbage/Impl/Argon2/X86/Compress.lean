import VerifiedGarbage.Spec.Argon2
import VerifiedGarbage.Impl.Blake2.X86.CompressB

/-!
# Argon2 compression G on x86 (32-bit)

`vg_argon2_compress(x, y, out, scratch)`, cdecl: the arguments are at
`[esp + 4]`, `[esp + 8]`, `[esp + 12]` and `[esp + 16]`.

* `esi` holds `scratch` throughout; the caller's `esi` is kept in
  `scratch[2048..2052)`. `[0, 1024)` holds R = X XOR Y, and `[1024, 2048)`
  the block P permutes (word `k` at `1024 + 8k`).
* Each 64-bit word is a pair of 32-bit words, the low one first (as in
  memory), as in `Impl/Blake2/X86/CompressB.lean`. Every step of GB reads its
  operands from scratch and writes its result back to it, with `eax`, `ecx`
  and `edx` as temporaries: `addMul` computes `a + b + 2 · lo(a) · lo(b)` with
  one `mul` (`EDX:EAX := EAX · EDX`), and `xorRot` rotates `d ^ a` as in
  BLAKE2b (`rorPair`: a rotation by 32 just swaps the halves).
* Every address is `esp`, `esi`, `ecx` or `edx` plus a constant, and there
  are no branches.
-/

namespace VG.Impl.Argon2.X86

open VG.X86
open VG.Impl.Sha512.X86 (at_ sc ld st add64 add64m)
open VG.Impl.Blake2.X86.CompressB (rorPair)

/-- `++`, grouping to the right (see `Impl/Blake2/X86/CompressB.lean`). -/
local infixr:65 " +++ " => HAppend.hAppend

/-- Where the caller's `esi` is kept. -/
def savedOff : Nat := 2048

/-- The word `k` of the permuted block. -/
def wOff (k : Nat) : Nat := 1024 + 8 * k

/-- `[esi + a] := addMul([esi + a], [esi + b])`: `edx:eax` gets the product
of the low halves (`mul edx`), doubled, then `b` and `a` are added. -/
def addMul (a b : Nat) : List Instr :=
  [.mov .edx (sc b), .mov .eax (sc a), .mul .edx] +++ add64 .eax .edx .eax .edx +++
    add64m .eax .edx b +++ add64m .eax .edx a +++ st .eax .edx a

/-- `(l, h) := (l, h) ^` the word at `[esi + o]`. -/
def xor64m (l h : Reg) (o : Nat) : List Instr := [.alu .xor l (sc o), .alu .xor h (sc (o + 4))]

/-- `(eax, edx) := [esi + d] ^ [esi + a]`. -/
def xorLd (d a : Nat) : List Instr := ld .eax .edx d +++ xor64m .eax .edx a

/-- `[esi + d] := ([esi + d] ^ [esi + a]) >>> 32`: the halves swapped. -/
def xorRot32 (d a : Nat) : List Instr := xorLd d a +++ st .edx .eax d

/-- `[esi + d] := ([esi + d] ^ [esi + a]) >>> n`, for `0 < n < 32`. -/
def xorRot (d a n : Nat) : List Instr := xorLd d a +++ rorPair .eax .edx n .ecx +++ st .edx .eax d

/-- `[esi + d] := ([esi + d] ^ [esi + a]) >>> 63`: a rotation by 31 of the
swapped halves. -/
def xorRot63 (d a : Nat) : List Instr := xorLd d a +++ rorPair .edx .eax 31 .ecx +++ st .eax .edx d

/-- GB (RFC 9106 §3.6) on the words at offsets `a, b, c, d` of scratch. -/
def gb (a b c d : Nat) : List Instr :=
  addMul a b +++ xorRot32 d a +++ addMul c d +++ xorRot b c 24 +++
  addMul a b +++ xorRot d a 16 +++ addMul c d +++ xorRot63 b c

/-- GB on words `a, b, c, d` of the permuted block. -/
def gbAt (a b c d : Nat) : Prog isa := .block (gb (wOff a) (wOff b) (wOff c) (wOff d))

/-- P over a row or column selected by `index`. -/
def permuteAt (index : Fin 16 → Fin 128) : Prog isa :=
  let step (a b c d : Fin 16) := gbAt (index a).val (index b).val (index c).val (index d).val
  .seq (step 0 4 8 12) <| .seq (step 1 5 9 13) <|
  .seq (step 2 6 10 14) <| .seq (step 3 7 11 15) <|
  .seq (step 0 5 10 15) <| .seq (step 1 6 11 12) <|
  .seq (step 2 7 8 13) (step 3 4 9 14)

/-- The rows, then the columns. -/
def rounds : Prog isa :=
  .seq ((List.finRange 8).foldr (fun row rest =>
    .seq (permuteAt (Spec.Argon2.rowIndex row)) rest) (.block [])) <|
  ((List.finRange 8).foldr (fun col rest =>
    .seq (permuteAt (Spec.Argon2.colIndex col)) rest) (.block []))

/-- Save `esi`, point it to scratch, and load `x` and `y` into `ecx` and `edx`. -/
def prologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 16)), .store (at_ .eax savedOff) .esi, .mov .esi (.reg .eax),
    .mov .ecx (.mem (at_ .esp 4)), .mov .edx (.mem (at_ .esp 8))]

/-- 32-bit word `i` of X XOR Y, to both halves of scratch. -/
def initWord (i : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ecx (4 * i))), .alu .xor .eax (.mem (at_ .edx (4 * i))),
    .store (at_ .esi (4 * i)) .eax, .store (at_ .esi (1024 + 4 * i)) .eax]

/-- 32-bit word `i` of the output: the permuted block XOR R, to `out` (`ecx`). -/
def finishWord (i : Nat) : List Instr :=
  [.mov .eax (sc (1024 + 4 * i)), .alu .xor .eax (sc (4 * i)), .store (at_ .ecx (4 * i)) .eax]

/-- Load `out`, write the output, and restore `esi`. -/
def epilogue : List Instr :=
  .mov .ecx (.mem (at_ .esp 12)) :: (List.range 256).flatMap finishWord +++
    [.mov .esi (sc savedOff)]

def compress : Prog isa :=
  .seq (.block (prologue +++ (List.range 256).flatMap initWord)) (.seq rounds (.block epilogue))

end VG.Impl.Argon2.X86
