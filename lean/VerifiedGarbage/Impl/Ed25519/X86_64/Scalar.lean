import VerifiedGarbage.Impl.X25519.X86_64

/-!
# Ed25519 scalar reduction on x86-64

Division by the constant subgroup order `L = 2^252 + c` (`c < 2^125`), a
64-bit word at a time, from the top: the remainder `r < L` becomes
`v = 2^64 r + w` for the next word `w`, which is `h 2^252 + l` with `h <
2^65`, so `v ≡ l + L - h c` (mod L) since `2^252 ≡ -c`, and `l + L - h c`
is below `2L` (`wordFold`); a subtraction of `L`, kept when there is no
borrow, leaves `v mod L`. All 8 words are processed, independent of their
values, with `mul`, additions, shifts and masks: no division instruction or
secret-dependent branch. `mul` overwrites `rdx`, so the loop keeps the
scratch in `rdi`, and the output's address at byte 48 of it.
-/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (at_ zero4 saved)

def orderLo : BitVec 64 := 0x5812631a5cf5d3ed
def orderHi : BitVec 64 := 0x14def9dea2f79cd6
def orderTop : BitVec 64 := 0x1000000000000000

/-- Save the original remainder and subtract L. -/
def scalarSubtract : List Instr :=
  [.mov .r12 (.reg .r8), .mov .r13 (.reg .r9), .mov .r14 (.reg .r10), .mov .r15 (.reg .r11),
    .movImm64 .rcx orderLo, .alu .sub .r8 (.reg .rcx),
    .movImm64 .rcx orderHi, .alu .sbb .r9 (.reg .rcx), .alu .sbb .r10 (.imm 0),
    .movImm64 .rcx orderTop, .alu .sbb .r11 (.reg .rcx)]

/-- Select the original remainder on borrow, the subtraction otherwise. -/
def scalarSelect : List Instr :=
  [.alu .sbb .rax (.reg .rax)] ++
  ([(Reg.r8, Reg.r12), (.r9, .r13), (.r10, .r14), (.r11, .r15)].flatMap fun (x, y) =>
    [.alu .xor y (.reg x), .alu .and y (.reg .rax), .alu .xor x (.reg y)])

/-- From `r = (r₀, r₁, r₂, r₃)` in r8–r11 and `w` in rax: `h₀ = r₂ >> 60 | 2^4 r₃` (rbp)
and `h₁ = r₃ >> 60` (r12), so that `h₀ + 2^64 h₁ = (2^64 r + w) >> 252`; and
`l = (w, r₀, r₁, r₂ mod 2^60)` into r8–r11. -/
def foldPrep : List Instr :=
  [.mov .rbp (.reg .r10), .shift .shr .rbp 60,
    .mov .rcx (.reg .r11), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .or .rbp (.reg .rcx),
    .mov .r12 (.reg .r11), .shift .shr .r12 60,
    .movImm64 .rcx 0x0fffffffffffffff, .alu .and .r10 (.reg .rcx),
    .mov .r11 (.reg .r10), .mov .r10 (.reg .r9), .mov .r9 (.reg .r8), .mov .r8 (.reg .rax)]

/-- `h₀ c` into r13–r15. -/
def foldMul : List Instr :=
  [.mov .rax (.reg .rbp), .movImm64 .rcx orderLo, .mul .rcx, .mov .r13 (.reg .rax),
    .mov .r14 (.reg .rdx),
    .mov .rax (.reg .rbp), .movImm64 .rcx orderHi, .mul .rcx, .alu .add .r14 (.reg .rax),
    .alu .adc .rdx (.imm 0), .mov .r15 (.reg .rdx)]

/-- `t = h c`: `2^64 c` added to r13–r15 under the mask `-h₁`. -/
def foldMask : List Instr :=
  [.mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .r12),
    .movImm64 .rax orderLo, .alu .and .rax (.reg .rcx), .movImm64 .rdx orderHi,
    .alu .and .rdx (.reg .rcx), .alu .add .r14 (.reg .rax), .alu .adc .r15 (.reg .rdx)]

/-- `u = L - t` into rax, rcx, rdx, rbp. -/
def foldSub : List Instr :=
  [.movImm64 .rax orderLo, .alu .sub .rax (.reg .r13),
    .movImm64 .rcx orderHi, .alu .sbb .rcx (.reg .r14),
    .mov32 .rdx (.imm 0), .alu .sbb .rdx (.reg .r15),
    .movImm64 .rbp orderTop, .alu .sbb .rbp (.imm 0)]

/-- `l + u` into r8–r11. -/
def foldAdd : List Instr :=
  [.alu .add .r8 (.reg .rax), .alu .adc .r9 (.reg .rcx), .alu .adc .r10 (.reg .rdx),
    .alu .adc .r11 (.reg .rbp)]

/-- From the remainder `r < L` in r8–r11 and the next word `w` in rax: `l + L - h c`, below
`2L` and congruent to `2^64 r + w`, for `2^64 r + w = h 2^252 + l`, into r8–r11. -/
def wordFold : List Instr := foldPrep ++ foldMul ++ foldMask ++ foldSub ++ foldAdd

/-- The next word, from the top (`rbx` counts its bytes down from 64), folded in. -/
def scalarWord : List Instr :=
  [.alu .sub .rbx (.imm 8), .mov .rax (.mem { base := .rsi, index := some .rbx })] ++
    wordFold ++ scalarSubtract ++ scalarSelect ++ [.alu .test .rbx (.reg .rbx)]

def scalarSave : List Instr := saved.map fun (r, d) => .store (at_ .rdx d) r
def scalarRestore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rdx d))

/-- The scratch from `rdi` back to `rdx`, and the output's address from byte 48 of it to
`rdi`. -/
def scalarFinishArgs : List Instr := [.mov .rdx (.reg .rdi), .mov .rdi (.mem (at_ .rdx 48))]

/-- `out = rdi`, the 64-byte input at rsi, scratch at rdx. -/
def scalarReduce : Prog isa :=
  .seq (.block (scalarSave ++ [.store (at_ .rdx 48) .rdi, .mov .rdi (.reg .rdx)] ++ zero4 ++
    [.mov32 .rbx (.imm 64)])) <|
  .seq (.loop (.block scalarWord) .ne) <|
    .block (scalarFinishArgs ++ scalarRestore ++ [.store (at_ .rdi 0) .r8, .store (at_ .rdi 8) .r9,
      .store (at_ .rdi 16) .r10, .store (at_ .rdi 24) .r11])

end VG.Impl.Ed25519.X86_64
