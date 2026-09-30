import VerifiedGarbage.Impl.Ed25519.AArch64.Word

/-! Binary reduction modulo the Ed25519 subgroup order, with 512 fixed
bit steps. No branch or address depends on the scalar. -/

namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def orderLo : BitVec 64 := 0x5812631a5cf5d3ed
def orderHi : BitVec 64 := 0x14def9dea2f79cd6
def orderTop : BitVec 64 := 0x1000000000000000

/-- x20 holds the current byte; x10 = 0 and x11 = 1. Comparing its bit
with 1 sets C to that bit before the four doubling-with-carry steps. -/
def scalarExtractBit (j : Nat) : List Instr :=
  [.lsr .x .x3 .x20 j, .logic .and .x .x3 .x3 .x11, .subs .x .x8 .x3 .x11]

def scalarDouble : List Instr :=
  [.adcs .x .x4 .x4 .x4, .adcs .x .x5 .x5 .x5,
    .adcs .x .x6 .x6 .x6, .adcs .x .x7 .x7 .x7]

def scalarShift (j : Nat) : List Instr := scalarExtractBit j ++ scalarDouble

def scalarSubtract : List Instr :=
  [mov .x21 .x4, mov .x22 .x5, mov .x23 .x6, mov .x24 .x7] ++
    const64 .x3 orderLo ++ [.subs .x .x4 .x4 .x3] ++
    const64 .x3 orderHi ++ [.sbcs .x .x5 .x5 .x3, .sbcs .x .x6 .x6 .x10] ++
    const64 .x3 orderTop ++ [.sbcs .x .x7 .x7 .x3]

def scalarSelect : List Instr :=
  [.sbcs .x .x8 .x10 .x10] ++
    ([(Reg.x4, Reg.x21), (.x5, .x22), (.x6, .x23), (.x7, .x24)].flatMap fun (x, y) =>
      [.logic .eor .x y y x, .logic .and .x y y .x8, .logic .eor .x x x y])

def scalarBit (j : Nat) : List Instr := scalarShift j ++ scalarSubtract ++ scalarSelect

def scalarByte : List Instr :=
  [.subImm .x .x19 .x19 1, .add .x .x9 .x1 .x19, .ldrb .x20 .x9 0] ++
    (List.range 8).reverse.flatMap scalarBit

def scalarSave : List Instr := saved.map fun (r, d) => .str .x r .x2 d
def scalarRestore : List Instr := saved.map fun (r, d) => .ldr .x r .x2 d

def scalarFinish : List Instr :=
  scalarRestore ++ [.str .x .x4 .x0 0, .str .x .x5 .x0 8,
    .str .x .x6 .x0 16, .str .x .x7 .x0 24]

def scalarInit : List Instr :=
  zero4 ++ [.movz .w .x10 0 0, .movz .w .x11 1 0, .movz .w .x19 64 0]

/-- `(out, wide, scratch) = (x0, x1, x2)`. -/
def scalarReduce : Prog isa :=
  .seq (.block (scalarSave ++ scalarInit)) <|
    .seq (.loop (.block scalarByte) (.nonzero .x .x19)) (.block scalarFinish)

end VG.Impl.Ed25519.AArch64
