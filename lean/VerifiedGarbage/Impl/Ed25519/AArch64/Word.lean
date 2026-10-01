import VerifiedGarbage.TCB.AArch64.Isa

/-! Four-word arithmetic for Ed25519 on baseline A64.

The workspace pointer is x0. Field words use x4–x7, the high half of a
product x21–x24, the row multiplicand x3, and its carry x20. x8/x2 hold
the low/high product, x9 is a loaded operand, x10 is zero, and x11 is 38.
x1 and x19 are available to the point and scalar loops. The six used
callee-saved registers x19–x24 are saved in the first 48 workspace bytes.

Field multiplication and squaring keep their operands in registers: the
words of one operand in x12–x15, the products in x2, x3, x8, x9, x11, x16
and x17, and the eight words of the full product in x4–x7 and x21–x24.
-/

namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def mov (d n : Reg) : Instr := .addImm .x d n 0

def const64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.movz .x d (v.extractLsb' 0 16) 0,
    .movk .x d (v.extractLsb' 16 16) 1,
    .movk .x d (v.extractLsb' 32 16) 2,
    .movk .x d (v.extractLsb' 48 16) 3]

def ld (r : Reg) (off : Nat) : Instr := .ldr .x r .x0 off
def st (r : Reg) (off : Nat) : Instr := .str .x r .x0 off

def saved : List (Reg × Nat) :=
  [(.x19, 0), (.x20, 8), (.x21, 16), (.x22, 24), (.x23, 32), (.x24, 40)]

def words : List Reg := [.x4, .x5, .x6, .x7, .x21, .x22, .x23, .x24]
def wordReg (i : Nat) : Reg := words.getD i .x4

def zero4 : List Instr :=
  [.movz .w .x4 0 0, .movz .w .x5 0 0, .movz .w .x6 0 0, .movz .w .x7 0 0]

def stores (o : Nat) (a b c d : Reg) : List Instr :=
  [st a o, st b (o + 8), st c (o + 16), st d (o + 24)]

def store4 (o : Nat) : List Instr := stores o .x4 .x5 .x6 .x7

def loads (o : Nat) (a b c d : Reg) : List Instr :=
  [ld a o, ld b (o + 8), ld c (o + 16), ld d (o + 24)]

/-- Add `ai * b + c` to the word `t`, putting the high word in `c`.
Requires x10 = 0 and distinct product/operand registers. -/
def mulStep (t c ai b : Reg) : List Instr :=
  [.mul .x .x8 ai b, .umulh .x2 ai b,
    .adds .x .x8 .x8 c, .adcs .x .x2 .x2 .x10,
    .adds .x t t .x8, .adcs .x .x2 .x2 .x10, mov c .x2]

def row (a b i : Nat) : List Instr :=
  [ld .x3 (a + 8 * i), .movz .w .x20 0 0] ++
    (List.range 4).flatMap (fun j =>
      [ld .x9 (b + 8 * j)] ++ mulStep (wordReg (i + j)) .x20 .x3 .x9) ++
    [mov (wordReg (i + 4)) .x20]

/-- Read carry as 0 or 38 in x8, with x10 = 0 and x11 = 38. -/
def carryValue38 : List Instr := [.adcs .x .x8 .x10 .x10, .mul .x .x8 .x8 .x11]

/-- Add x8 to x4–x7, folding its last carry using 2^256 = 38 modulo p. -/
def carry38 : List Instr :=
  [.adds .x .x4 .x4 .x8, .adcs .x .x5 .x5 .x10,
    .adcs .x .x6 .x6 .x10, .adcs .x .x7 .x7 .x10] ++
    carryValue38 ++ [.add .x .x4 .x4 .x8]

def fold : List Instr := [.mul .x .x8 .x20 .x11] ++ carry38

/-- `t0 + 2⁶⁴ t1 + 2¹²⁸ t2 + 2¹⁹² t3 + a · (b0 + … + 2¹⁹² b3)` into `t0`–`t4`,
with x10 = 0: the low halves of the products added in one carry chain, and
the high halves one word up in another. -/
def rowAcc (a b0 b1 b2 b3 t0 t1 t2 t3 t4 : Reg) : List Instr :=
  [.mul .x .x2 a b0, .mul .x .x8 a b1, .mul .x .x9 a b2, .mul .x .x16 a b3,
    .adds .x t0 t0 .x2, .adcs .x t1 t1 .x8, .adcs .x t2 t2 .x9, .adcs .x t3 t3 .x16,
    .adcs .x t4 .x10 .x10,
    .umulh .x2 a b0, .umulh .x8 a b1, .umulh .x9 a b2, .umulh .x16 a b3,
    .adds .x t1 t1 .x2, .adcs .x t2 t2 .x8, .adcs .x t3 t3 .x9, .adcs .x t4 t4 .x16]

/-- `a · (b0 + … + 2¹⁹² b3)` into `t0`–`t4`, with x10 = 0. -/
def rowFirst (a b0 b1 b2 b3 t0 t1 t2 t3 t4 : Reg) : List Instr :=
  [.mul .x t0 a b0, .mul .x t1 a b1, .mul .x t2 a b2, .mul .x t3 a b3,
    .umulh .x2 a b0, .umulh .x8 a b1, .umulh .x9 a b2, .umulh .x16 a b3,
    .adds .x t1 t1 .x2, .adcs .x t2 t2 .x8, .adcs .x t3 t3 .x9, .adcs .x t4 .x16 .x10]

/-- The eight-word product of the field elements at `a` and `b`, with x10 = 0. -/
def mulWide (a b : Nat) : List Instr :=
  loads b .x12 .x13 .x14 .x15 ++
    [ld .x3 a] ++ rowFirst .x3 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21 ++
    [ld .x3 (a + 8)] ++ rowAcc .x3 .x12 .x13 .x14 .x15 .x5 .x6 .x7 .x21 .x22 ++
    [ld .x3 (a + 16)] ++ rowAcc .x3 .x12 .x13 .x14 .x15 .x6 .x7 .x21 .x22 .x23 ++
    [ld .x3 (a + 24)] ++ rowAcc .x3 .x12 .x13 .x14 .x15 .x7 .x21 .x22 .x23 .x24

/-- The products `aᵢ aⱼ` (`i < j`) of the words x12–x15, at their word
`i + j` of x4–x7, x21–x24 less one: into x5–x7, x21–x23, with x10 = 0. -/
def sqrCross : List Instr :=
  [.mul .x .x5 .x12 .x13, .mul .x .x6 .x12 .x14, .mul .x .x7 .x12 .x15,
    .umulh .x2 .x12 .x13, .umulh .x8 .x12 .x14, .umulh .x9 .x12 .x15,
    .adds .x .x6 .x6 .x2, .adcs .x .x7 .x7 .x8, .adcs .x .x21 .x9 .x10,
    .mul .x .x2 .x13 .x14, .mul .x .x8 .x13 .x15, .umulh .x9 .x13 .x14, .umulh .x16 .x13 .x15,
    .adds .x .x7 .x7 .x2, .adcs .x .x21 .x21 .x8, .adcs .x .x22 .x16 .x10,
    .adds .x .x21 .x21 .x9, .adcs .x .x22 .x22 .x10,
    .mul .x .x2 .x14 .x15, .umulh .x8 .x14 .x15,
    .adds .x .x22 .x22 .x2, .adcs .x .x23 .x8 .x10]

/-- Double x5–x7, x21–x23 into x5–x7, x21–x24, with x10 = 0. -/
def sqrDouble : List Instr :=
  [.adds .x .x5 .x5 .x5, .adcs .x .x6 .x6 .x6, .adcs .x .x7 .x7 .x7,
    .adcs .x .x21 .x21 .x21, .adcs .x .x22 .x22 .x22, .adcs .x .x23 .x23 .x23,
    .adcs .x .x24 .x10 .x10]

/-- Add the squares `aᵢ²` of the words x12–x15 at word `2 i`, setting x4. -/
def sqrDiag : List Instr :=
  [.mul .x .x4 .x12 .x12, .umulh .x2 .x12 .x12, .mul .x .x8 .x13 .x13, .umulh .x9 .x13 .x13,
    .mul .x .x16 .x14 .x14, .umulh .x17 .x14 .x14, .mul .x .x3 .x15 .x15, .umulh .x11 .x15 .x15,
    .adds .x .x5 .x5 .x2, .adcs .x .x6 .x6 .x8, .adcs .x .x7 .x7 .x9, .adcs .x .x21 .x21 .x16,
    .adcs .x .x22 .x22 .x17, .adcs .x .x23 .x23 .x3, .adcs .x .x24 .x24 .x11]

/-- The eight-word square of the field element at `a`, with x10 = 0. -/
def sqrWide (a : Nat) : List Instr :=
  loads a .x12 .x13 .x14 .x15 ++ sqrCross ++ sqrDouble ++ sqrDiag

/-- Reduce the eight words x4–x7, x21–x24 modulo p into x4–x7, with x10 = 0:
add 38 times the high half to the low half, then fold the carry word. -/
def reduceWide : List Instr :=
  [.movz .w .x11 38 0] ++ rowAcc .x11 .x21 .x22 .x23 .x24 .x4 .x5 .x6 .x7 .x20 ++ fold

def fieldMul (o a b : Nat) : List Instr :=
  [.movz .w .x10 0 0] ++ mulWide a b ++ reduceWide ++ store4 o

def fieldSqr (o a : Nat) : List Instr :=
  [.movz .w .x10 0 0] ++ sqrWide a ++ reduceWide ++ store4 o

def fieldAddWords (a b : Nat) : List Instr :=
  [ld .x4 a, ld .x9 b, .adds .x .x4 .x4 .x9,
    ld .x5 (a + 8), ld .x9 (b + 8), .adcs .x .x5 .x5 .x9,
    ld .x6 (a + 16), ld .x9 (b + 16), .adcs .x .x6 .x6 .x9,
    ld .x7 (a + 24), ld .x9 (b + 24), .adcs .x .x7 .x7 .x9] ++
    carryValue38

def fieldAdd (o a b : Nat) : List Instr :=
  [.movz .w .x10 0 0, .movz .w .x11 38 0] ++ fieldAddWords a b ++ carry38 ++ store4 o

/-- Read the no-borrow flag as 0, or 38 when there was a borrow. -/
def borrowValue38 : List Instr :=
  [.sbcs .x .x8 .x10 .x10, .logic .and .x .x8 .x8 .x11]

def fieldSubWords (a b : Nat) : List Instr :=
  [ld .x4 a, ld .x9 b, .subs .x .x4 .x4 .x9,
    ld .x5 (a + 8), ld .x9 (b + 8), .sbcs .x .x5 .x5 .x9,
    ld .x6 (a + 16), ld .x9 (b + 16), .sbcs .x .x6 .x6 .x9,
    ld .x7 (a + 24), ld .x9 (b + 24), .sbcs .x .x7 .x7 .x9] ++ borrowValue38

def borrow38 : List Instr :=
  [.subs .x .x4 .x4 .x8, .sbcs .x .x5 .x5 .x10,
    .sbcs .x .x6 .x6 .x10, .sbcs .x .x7 .x7 .x10] ++ borrowValue38

def fieldSub (o a b : Nat) : List Instr :=
  [.movz .w .x10 0 0, .movz .w .x11 38 0] ++ fieldSubWords a b ++ borrow38 ++
    [.sub .x .x4 .x4 .x8] ++ store4 o

def low63 : BitVec 64 := 0x7fffffffffffffff

/-- Fold the high bit into 19, given x2 = low63, x10 = 0 and x11 = 19. -/
def freezeFold : List Instr :=
  [.lsr .x .x8 .x7 63, .logic .and .x .x7 .x7 .x2, .mul .x .x3 .x8 .x11,
    .adds .x .x4 .x4 .x3, .adcs .x .x5 .x5 .x10,
    .adcs .x .x6 .x6 .x10, .adcs .x .x7 .x7 .x10]

/-- Compute x - p as a candidate, and the mask selecting it. -/
def freezeCandidate : List Instr :=
  [.adds .x .x21 .x4 .x11, .adcs .x .x22 .x5 .x10,
    .adcs .x .x23 .x6 .x10, .adcs .x .x24 .x7 .x10,
    .lsr .x .x8 .x24 63, .logic .and .x .x24 .x24 .x2, .sub .x .x3 .x10 .x8]

def select4 : List Instr :=
  [(Reg.x4, Reg.x21), (.x5, .x22), (.x6, .x23), (.x7, .x24)].flatMap fun (x, y) =>
    [.logic .eor .x y y x, .logic .and .x y y .x3, .logic .eor .x x x y]

/-- Fully reduce the field element at `a` into x4–x7. -/
def freeze (a : Nat) : List Instr :=
  [.movz .w .x10 0 0, .movz .w .x11 19 0] ++ const64 .x2 low63 ++
    loads a .x4 .x5 .x6 .x7 ++ freezeFold ++ freezeCandidate ++ select4

def swapWord (a b : Reg) : List Instr :=
  [.logic .eor .x .x8 a b, .logic .and .x .x8 .x8 .x3,
    .logic .eor .x a a .x8, .logic .eor .x b b .x8]

def swapWords : List Instr :=
  [(Reg.x4, Reg.x21), (.x5, .x22), (.x6, .x23), (.x7, .x24)].flatMap fun (a, b) => swapWord a b

/-- Swap two field elements if x3 is all ones, leaving them if it is zero. -/
def cswap (x y : Nat) : List Instr :=
  loads x .x4 .x5 .x6 .x7 ++ loads y .x21 .x22 .x23 .x24 ++
    swapWords ++
    store4 x ++ stores y .x21 .x22 .x23 .x24

end VG.Impl.Ed25519.AArch64
