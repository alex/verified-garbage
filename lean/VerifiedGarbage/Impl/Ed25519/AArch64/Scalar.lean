import VerifiedGarbage.Impl.Ed25519.AArch64.Word

/-!
# Ed25519 scalar reduction on AArch64

Division by the constant subgroup order `L = 2^252 + c` (`c < 2^125`), a
64-bit word at a time, from the top: the remainder `r < L` becomes
`v = 2^64 r + w` for the next word `w`, which is `h 2^252 + l` with
`h < 2^65`, so `v ≡ l + L - h c` (mod L) since `2^252 ≡ -c`, and
`l + L - h c` is below `2L` (`wordFold`); a subtraction of `L`, kept when
there is no borrow, leaves `v mod L`. All 8 words are processed,
independent of their values, with `mul`, `umulh`, additions, shifts and
masks: no division instruction or secret-dependent branch or address.
-/

namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def orderLo : BitVec 64 := 0x5812631a5cf5d3ed
def orderHi : BitVec 64 := 0x14def9dea2f79cd6
def orderTop : BitVec 64 := 0x1000000000000000

def scalarSubtract : List Instr :=
  [mov .x21 .x4, mov .x22 .x5, mov .x23 .x6, mov .x24 .x7] ++
    const64 .x3 orderLo ++ [.subs .x .x4 .x4 .x3] ++
    const64 .x3 orderHi ++ [.sbcs .x .x5 .x5 .x3, .sbcs .x .x6 .x6 .x10] ++
    const64 .x3 orderTop ++ [.sbcs .x .x7 .x7 .x3]

def scalarSelect : List Instr :=
  [.sbcs .x .x8 .x10 .x10] ++
    ([(Reg.x4, Reg.x21), (.x5, .x22), (.x6, .x23), (.x7, .x24)].flatMap fun (x, y) =>
      [.logic .eor .x y y x, .logic .and .x y y .x8, .logic .eor .x x x y])

/-- From `r = (r₀, r₁, r₂, r₃)` in x4–x7 and `w` in x3: `h₀ = r₂ >> 60 | 2^4 r₃` (x12)
and `h₁ = r₃ >> 60` (x13), so that `h₀ + 2^64 h₁ = (2^64 r + w) >> 252`; and
`l = (w, r₀, r₁, r₂ mod 2^60)` into x4–x7. -/
def foldPrep : List Instr :=
  [.lsr .x .x12 .x6 60, .lsl .x .x13 .x7 4, .logic .orr .x .x12 .x12 .x13,
    .lsr .x .x13 .x7 60, .lsl .x .x7 .x6 4, .lsr .x .x7 .x7 4,
    mov .x6 .x5, mov .x5 .x4, mov .x4 .x3]

/-- The low two words of `c`, in x8 and x17. -/
def foldConst : List Instr := const64 .x8 orderLo ++ const64 .x17 orderHi

/-- `h₀ c` into x14–x16. -/
def foldMul : List Instr :=
  [.mul .x .x14 .x12 .x8, .umulh .x15 .x12 .x8, .mul .x .x9 .x12 .x17, .umulh .x16 .x12 .x17,
    .adds .x .x15 .x15 .x9, .adcs .x .x16 .x16 .x10]

/-- `t = h c`: `2^64 h₁ c` added to x14–x16, as `h₁ ≤ 1` times each word of `c`. -/
def foldHigh : List Instr :=
  [.mul .x .x9 .x13 .x8, .mul .x .x13 .x13 .x17,
    .adds .x .x15 .x15 .x9, .adcs .x .x16 .x16 .x13]

/-- `u = L - t` into x14–x16 and x9. -/
def foldSub : List Instr :=
  [.subs .x .x14 .x8 .x14, .sbcs .x .x15 .x17 .x15, .sbcs .x .x16 .x10 .x16,
    .movz .x .x9 0x1000 3, .sbcs .x .x9 .x9 .x10]

/-- `l + u` into x4–x7. -/
def foldAdd : List Instr :=
  [.adds .x .x4 .x4 .x14, .adcs .x .x5 .x5 .x15, .adcs .x .x6 .x6 .x16, .adcs .x .x7 .x7 .x9]

/-- From the remainder `r < L` in x4–x7 and the next word `w` in x3: `l + L - h c`, below
`2L` and congruent to `2^64 r + w`, for `2^64 r + w = h 2^252 + l`, into x4–x7.
Requires x10 = 0. -/
def wordFold : List Instr := foldPrep ++ foldConst ++ foldMul ++ foldHigh ++ foldSub ++ foldAdd

/-- The next word, from the top (x19 counts its bytes down from 64), folded in. -/
def scalarWord : List Instr :=
  [.subImm .x .x19 .x19 8, .add .x .x9 .x1 .x19, .ldr .x .x3 .x9 0] ++
    wordFold ++ scalarSubtract ++ scalarSelect

def scalarSave : List Instr := saved.map fun (r, d) => .str .x r .x2 d
def scalarRestore : List Instr := saved.map fun (r, d) => .ldr .x r .x2 d

def scalarFinish : List Instr :=
  scalarRestore ++ [.str .x .x4 .x0 0, .str .x .x5 .x0 8,
    .str .x .x6 .x0 16, .str .x .x7 .x0 24]

def scalarInit : List Instr :=
  zero4 ++ [.movz .w .x10 0 0, .movz .w .x19 64 0]

/-- `(out, wide, scratch) = (x0, x1, x2)`. -/
def scalarReduce : Prog isa :=
  .seq (.block (scalarSave ++ scalarInit)) <|
    .seq (.loop (.block scalarWord) (.nonzero .x .x19)) (.block scalarFinish)

end VG.Impl.Ed25519.AArch64
