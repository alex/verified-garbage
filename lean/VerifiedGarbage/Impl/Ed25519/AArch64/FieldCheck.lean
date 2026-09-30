import VerifiedGarbage.Impl.Ed25519.AArch64.Field

/-! Public-input equality tests. x8 is zero exactly when the words are zero. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def wordsZero : List Instr :=
  [.logic .orr .x .x8 .x4 .x5, .logic .orr .x .x8 .x8 .x6, .logic .orr .x .x8 .x8 .x7]

def fieldZero (a : Slot) : List Instr := freeze (offset a) ++ wordsZero
def fieldEqual (a b : Slot) : List Instr := fieldCode [.sub 21 a b] ++ fieldZero 21

end VG.Impl.Ed25519.AArch64
