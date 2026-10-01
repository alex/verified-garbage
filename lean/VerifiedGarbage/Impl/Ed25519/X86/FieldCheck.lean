import VerifiedGarbage.Impl.Ed25519.X86.Field

namespace VG.Impl.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86

def wordOr (o j : Nat) : List Instr :=
  [.mov .edx (.mem (sc (o + 4 * j))), .alu .or .eax (.reg .edx)]

def wordsZero (o : Nat) : List Instr :=
  [.mov .eax (.imm 0)] ++ (List.range 8).flatMap (wordOr o) ++ [.alu .test .eax (.reg .eax)]

def fieldZero (a : Slot) : List Instr := freeze (offset a) ++ wordsZero (offset a)
def fieldEqual (a b : Slot) : List Instr := fieldCode [.sub 21 a b] ++ fieldZero 21

end VG.Impl.Ed25519.X86
