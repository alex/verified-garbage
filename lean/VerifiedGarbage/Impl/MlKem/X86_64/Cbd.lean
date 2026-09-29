import VerifiedGarbage.Impl.MlKem.X86_64.Common

/-!
# ML-KEM on x86-64: `vg_mlkem_cbd2`

`cbd2(b = rdi, f = rsi)` runs over the 128 bytes of `b`, with `rcx`
counting down; each byte `c` gives two coefficients, from its nibbles. The
sums of pairs of bits, `t = (c ∧ 0x55) + ((c >> 1) ∧ 0x55)`, hold `x₀`,
`y₀`, `x₁` and `y₁` of `SamplePolyCBD₂` in their 2-bit fields (each is at
most 2); coefficient `2j` is `x₀ + q - y₀` and coefficient `2j + 1` is
`x₁ + q - y₁`, each reduced with `csubQ`. Every address and branch depends
only on the pointers.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- The pair sums of the byte at `rdi`, in `rax`. -/
def cbdLoad : List Instr :=
  [.movzx8 .rax (at_ .rdi 0), .mov32 .rdx (.reg .rax), .shift32 .shr .rdx 1, .alu32 .and .rax (.imm 0x55),
    .alu32 .and .rdx (.imm 0x55), .alu32 .add .rax (.reg .rdx)]

/-- Coefficient `2j`, from the low nibble, to `[rsi]`. -/
def cbdLo : List Instr :=
  [.mov32 .rdx (.reg .rax), .alu32 .and .rdx (.imm 3), .alu32 .add .rdx (.imm qImm), .mov32 .r8 (.reg .rax),
    .shift32 .shr .r8 2, .alu32 .and .r8 (.imm 3), .alu32 .sub .rdx (.reg .r8)] ++ csubQ .rdx .r9 ++
    [.store32 (at_ .rsi 0) .rdx]

/-- Coefficient `2j + 1`, from the high nibble, to `[rsi + 4]`. -/
def cbdHi : List Instr :=
  [.mov32 .rdx (.reg .rax), .shift32 .shr .rdx 4, .alu32 .and .rdx (.imm 3), .alu32 .add .rdx (.imm qImm),
    .shift32 .shr .rax 6, .alu32 .sub .rdx (.reg .rax)] ++ csubQ .rdx .r9 ++ [.store32 (at_ .rsi 4) .rdx]

def cbdStep : List Instr := [.alu .add .rdi (.imm 1), .alu .add .rsi (.imm 8), .alu .sub .rcx (.imm 1)]

def cbd2Body : List Instr := cbdLoad ++ cbdLo ++ cbdHi ++ cbdStep

def cbd2 : Prog isa := .seq (.block [.mov32 .rcx (.imm 128)]) (.loop (.block cbd2Body) .ne)

end VG.Impl.MlKem.X86_64
