import VerifiedGarbage.Impl.Ed25519.Arm.Freeze
import VerifiedGarbage.Impl.Ed25519.Arm.Field

/-! Public field comparisons through their canonical sixteen-bit limbs. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def sumLimb (o k : Nat) : List Instr := [.ldr .r3 .r0 (o + 4 * k), .dp .add .r9 .r9 (.reg .r3)]
def wordsZero (o : Nat) : List Instr :=
  [.mov .r9 (.imm 0)] ++ (List.range 16).flatMap (sumLimb o) ++ [.cmp .r9 (.imm 0)]

def fieldZero (a : Slot) : Prog isa := .seq (.block (freeze a)) (.block (wordsZero FR))
def fieldEqual (a b : Slot) : Prog isa := .seq (fieldCode [.sub 21 a b]) (fieldZero 21)

def equalLimb (a b k : Nat) : List Instr :=
  [.ldr .r3 .r0 (a + 4 * k), .ldr .r2 .r0 (b + 4 * k),
    .dp .eor .r3 .r3 (.reg .r2), .dp .orr .r9 .r9 (.reg .r3)]

def wordsEqual (a b : Nat) : List Instr :=
  [.mov .r9 (.imm 0)] ++ (List.range 16).flatMap (equalLimb a b) ++ [.cmp .r9 (.imm 0)]

end VG.Impl.Ed25519.Arm
