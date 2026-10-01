import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.TCB.AArch64.Isa

/-! # RC2 selection on baseline AArch64

Every candidate is visited in a fixed order. Secret indices are used only
in arithmetic masks, never as addresses or branch conditions.
-/

namespace VG.Impl.Rc2.AArch64

open VG.AArch64

def rr (dst src : Reg) : Instr := .addImm .x dst src 0
def imm (dst : Reg) (n : Nat) : Instr := .movz .x dst (BitVec.ofNat 16 n) 0

/-- Keep the low `n` bits without needing a logical-immediate instruction. -/
def mask (r : Reg) (n : Nat) : List Instr :=
  [.lsl .x r r (64 - n), .lsr .x r r (64 - n)]

/-- Equality mask for byte `x8` and candidate `i`, returned in `x7`. -/
def selectMask (i : Nat) : List Instr :=
  [imm .x6 i, .logic .eor .x .x6 .x8 .x6, .subImm .x .x6 .x6 1,
   .lsr .x .x6 .x6 63, imm .x7 0, .sub .x .x7 .x7 .x6]

def piStep (i : Nat) : List Instr :=
  selectMask i ++
    ([imm .x6 (Spec.Rc2.piTable.getD i 0).toNat,
      .logic .and .x .x7 .x7 .x6, .logic .orr .x .x3 .x3 .x7] : List Instr)

/-- PITABLE of the low byte of `x8`, returned in `x8`. -/
def piLookup : List Instr :=
  mask .x8 8 ++ [imm .x3 0] ++ (List.range 256).flatMap piStep ++ [rr .x8 .x3]

/-- Load schedule word `i` at `x0` into `x4`, using byte accesses. -/
def loadKey (i : Nat) : List Instr :=
  [.ldrb .x4 .x0 (2 * i), .ldrb .x5 .x0 (2 * i + 1),
   .ror .x .x5 .x5 56, .logic .orr .x .x4 .x4 .x5]

def keyStep (i : Nat) : List Instr :=
  selectMask i ++ loadKey i ++
    ([.logic .and .x .x4 .x4 .x7, .logic .orr .x .x3 .x3 .x4] : List Instr)

/-- Select schedule word `x8 & 63`, returned in `x8`. -/
def keyLookup : List Instr :=
  mask .x8 6 ++ [imm .x3 0] ++ (List.range 64).flatMap keyStep ++ [rr .x8 .x3]

end VG.Impl.Rc2.AArch64
