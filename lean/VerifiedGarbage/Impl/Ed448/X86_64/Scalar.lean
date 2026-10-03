import VerifiedGarbage.Impl.X448.X86_64

/-!
# Ed448 scalar arithmetic on x86-64

Arithmetic modulo the subgroup order `L = 2^446 - c` (`c < 2^224`), on a
remainder of seven words in `r8–r14` (X448's `W`).

Reduction consumes the input a 64-bit word at a time, from the top: the
remainder `r < L` becomes `v = 2^64 r + w` for the next word `w`, which is
`h 2^446 + l` with `h < 2^64`, so `v ≡ l + h c` (mod L) since
`2^446 ≡ c`, and `l + h c` is below `2^446 + 2^288 < 2L` (`wordFold`). A
conditional subtraction of `L` (`csub`) leaves `v mod L`: the remainder is
saved at `TMP`, `K = 2^448 - L` (stored at `KC`) added, which carries out
of 448 bits exactly when `v ≥ L`, and the sum or the saved remainder
selected with the mask `-carry`, as X448's `freeze` does.

Multiply-add reduces its three inputs, multiplies two of them with X448's
product scanning (`columns`, into `ACC`), reduces the product's fourteen
words, and adds the third, with a last conditional subtraction.

Every step runs for all words, independent of their values, with `mul`,
additions, rotations and masks: no division instruction, no branch but on
the loop counter `rbx`, and every address a pointer plus a constant or the
counter. The working space's base is in `rdi`; the callee-saved registers
are saved in its first 48 bytes, and the arguments from byte 48.
-/

namespace VG.Impl.Ed448.X86_64

open VG.X86_64
open VG.Impl.X448.X86_64 (at_ sc W w loads stores chain mulSteps saved)

/-! ## The layout of the working space -/

/-- The output's address. -/
def OUT : Nat := 48
/-- The arguments `r`, `k` and `s` of multiply-add. -/
def ARG_R : Nat := 56
def ARG_K : Nat := 64
def ARG_S : Nat := 72
/-- `K = 2^448 - L`. -/
def KC : Nat := 128
/-- The remainder saved by `csub`. -/
def TMP : Nat := 192
/-- The reduced `k`, `s` and `r` of multiply-add. -/
def SK : Nat := 256
def SS : Nat := 320
def SR : Nat := 384

/-! ## Constants -/

/-- The words of `c = 2^446 - L`, lowest first. -/
def cWords : List (BitVec 64) :=
  [0xdc873d6d54a7bb0d, 0xde933d8d723a70aa, 0x3bb124b65129c96f, 0x8335dc16]

/-- The words of `K = 2^448 - L = 3 · 2^446 + c`, lowest first. -/
def kWords : List (BitVec 64) :=
  [0xdc873d6d54a7bb0d, 0xde933d8d723a70aa, 0x3bb124b65129c96f, 0x8335dc16, 0, 0,
    0xc000000000000000]

/-- The words of `K` into `r8–r14`. -/
def loadK : List Instr := (W.zip kWords).map fun (r, v) => .movImm64 r v

/-- `K` stored at `KC`. -/
def storeK : List Instr := loadK ++ stores KC W

/-! ## One word -/

/-- From the remainder `r = (r₀, …, r₆)` in `r8–r14` and the next word `w`
in `rax`: `h = r₅ >> 62 + 4 r₆` into `rcx` (`r₆ < 2^62`, so rotating it
right by 62 shifts it left by 2), and `l = (w, r₀, …, r₄, r₅ mod 2^62)`
into `r8–r14`; `rbp = 0`. -/
def foldPrep : List Instr :=
  [.mov .rcx (.reg .r13), .shift .shr .rcx 62, .mov .rbp (.reg .r14), .shift .ror .rbp 62,
    .alu .add .rcx (.reg .rbp), .movImm64 .rbp 0x3fffffffffffffff, .alu .and .r13 (.reg .rbp),
    .mov .r14 (.reg .r13), .mov .r13 (.reg .r12), .mov .r12 (.reg .r11), .mov .r11 (.reg .r10),
    .mov .r10 (.reg .r9), .mov .r9 (.reg .r8), .mov .r8 (.reg .rax), .mov32 .rbp (.imm 0)]

/-- `l + h c`: multiply-accumulate steps of `rcx = h` by the words of `c`
into `r8–r11`, and their carry `rbp` added to `r12–r14`. -/
def foldMul : List Instr :=
  mulSteps [.r8, .r9, .r10, .r11] (cWords.map (.movImm64 .rax ·)) ++
    chain .add .adc [.r12, .r13, .r14] [.reg .rbp, .imm 0, .imm 0]

/-- `2^64 r + w`, reduced below `2L`. -/
def wordFold : List Instr := foldPrep ++ foldMul

/-- `r8–r14` (below `2L`) reduced modulo `L`: saved at `TMP`, `K` added,
and the sum (if it carried) or the saved value selected. -/
def csub : List Instr :=
  stores TMP W ++ chain .add .adc W ((List.range 7).map fun i => .mem (sc (KC + 8 * i))) ++
    [.alu .sbb .r15 (.reg .r15)] ++
    (List.range 7).flatMap fun i =>
      [.mov .rax (.mem (sc (TMP + 8 * i))), .alu .xor (w i) (.reg .rax),
        .alu .and (w i) (.reg .r15), .alu .xor (w i) (.reg .rax)]

/-- The next word from the top (`rbx` counts the input's bytes down), folded
in and reduced. -/
def scalarWord : List Instr :=
  [.alu .sub .rbx (.imm 8), .mov .rax (.mem { base := .rsi, index := some .rbx })] ++
    wordFold ++ csub ++ [.alu .test .rbx (.reg .rbx)]

/-- The loop over the words below `rbx`. -/
def scalarLoop : Prog isa := .loop (.block scalarWord) .ne

/-! ## Reducing an input -/

/-- `r9–r14 = 0`. -/
def zeroHigh : List Instr := [.r9, .r10, .r11, .r12, .r13, .r14].map fun r => .mov32 r (.imm 0)

/-- The top byte of the 57 bytes at `rsi` as the remainder, and the count of
the bytes below it. -/
def init57 : List Instr :=
  .movzx8 .r8 (at_ .rsi 56) :: zeroHigh ++ [.mov32 .rbx (.imm 56)]

/-- The remainder of the 57 bytes at `rsi`: their top byte, then the seven
words below it. -/
def reduce57 : Prog isa := .seq (.block init57) scalarLoop

/-- The top two bytes of the 114 bytes at `rsi` as the remainder, and the
count of the bytes below them. -/
def init114 : List Instr :=
  .movzx8 .r8 (at_ .rsi 112) :: .movzx8 .rax (at_ .rsi 113) :: .shift .ror .rax 56 ::
    .alu .add .r8 (.reg .rax) :: zeroHigh ++ [.mov32 .rbx (.imm 112)]

/-- The remainder of the 114 bytes at `rsi`: their top two bytes, then the
fourteen words below them. -/
def reduce114 : Prog isa := .seq (.block init114) scalarLoop

/-! ## Entry and exit -/

/-- Saves the callee-saved registers at `[b]`. -/
def saveAt (b : Reg) : List Instr := saved.map fun (r, d) => .store (at_ b d) r

/-- The remainder in `r8–r14` to the 57 bytes at the output's address
(saved at `OUT`): seven words and a zero byte; then the callee-saved
registers restored (as X448 restores them). -/
def finish : List Instr :=
  [.mov .rax (.mem (sc OUT))] ++ (List.range 7).map (fun i => .store (at_ .rax (8 * i)) (w i)) ++
    [.mov32 .rcx (.imm 0), .store8 (at_ .rax 56) .rcx] ++ Impl.X448.X86_64.restore

/-- `vg_ed448_scalar_reduce(out = rdi, wide = rsi, scratch = rdx)`. -/
def scalarReduce : Prog isa :=
  .seq (.block (saveAt .rdx ++ [.store (at_ .rdx OUT) .rdi, .mov .rdi (.reg .rdx)] ++ storeK)) <|
  .seq reduce114 (.block finish)

/-- The arguments of multiply-add saved in the working space (`r8`), and
its base into `rdi`. -/
def saveArgs : List Instr :=
  [.store (at_ .r8 OUT) .rdi, .store (at_ .r8 ARG_R) .rsi, .store (at_ .r8 ARG_K) .rdx,
    .store (at_ .r8 ARG_S) .rcx, .mov .rdi (.reg .r8)]

/-- The product of `[SK]` and `[SS]` into `ACC`. -/
def product : List Instr :=
  loads SS W ++ Impl.X448.X86_64.zeroAcc ++
    Impl.X448.X86_64.columns (fun i => .mem (sc (SK + 8 * i))) w Impl.X448.X86_64.mulCol

/-- The loop over the product's words: from `rdi + ACC`, with a zero
remainder. -/
def accInit : List Instr :=
  .mov .rsi (.reg .rdi) :: .alu .add .rsi (.imm (BitVec.ofNat 32 Impl.X448.X86_64.ACC)) ::
    .mov32 .r8 (.imm 0) :: zeroHigh ++ [.mov32 .rbx (.imm 112)]

/-- `vg_ed448_scalar_mul_add(out = rdi, r = rsi, k = rdx, s = rcx, scratch = r8)`:
`k mod L` to `SK`, `s mod L` to `SS`, `r mod L` to `SR`; their product's
fourteen words at `ACC`, reduced, plus `SR`, reduced. -/
def scalarMulAdd : Prog isa :=
  .seq (.block (saveAt .r8 ++ (saveArgs ++ (storeK ++ [.mov .rsi (.mem (sc ARG_K))])))) <|
  .seq reduce57 <| .seq (.block (stores SK W ++ [.mov .rsi (.mem (sc ARG_S))])) <|
  .seq reduce57 <| .seq (.block (stores SS W ++ [.mov .rsi (.mem (sc ARG_R))])) <|
  .seq reduce57 <|
  .seq (.block (stores SR W ++ (product ++ accInit))) <|
  .seq scalarLoop <|
    .block (chain .add .adc W ((List.range 7).map fun i => .mem (sc (SR + 8 * i))) ++ (csub ++
      finish))

end VG.Impl.Ed448.X86_64
