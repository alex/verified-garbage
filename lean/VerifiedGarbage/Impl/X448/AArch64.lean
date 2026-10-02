import VerifiedGarbage.Impl.X448.AArch64.Tail

/-!
# X448: AArch64 implementation

`vg_x448(out = x0, scalar = x1, point = x2, scratch = x3)`.

Field elements are sixteen normalized 28-bit limbs in 64-bit words.
Multiplication packs them into eight 56-bit limbs, accumulates two-word product
coefficients in registers, folding with
`2^448 = 2^224 + 1`. Squaring computes each cross product once. One wide
carry pass and two narrow passes restore normalized 28-bit slots. Pointwise
operations fuse coefficient arithmetic with their first carry pass. The ladder and
inversion addition chain follow the same arithmetic as the x86-64 baseline.

`x3` holds the working space, `x1` the output pointer after scalar decoding,
`x19` the ladder or squaring counter. Multiplication uses caller-saved
registers for its operands and coefficients.
`x20` saves the output pointer during setup. The two callee-saved registers
are saved in the working space and restored before returning. `x12` holds
`2^28 - 1` throughout. Only pointers and counters affect addresses or branches.
-/

namespace VG.Impl.X448.AArch64

open VG.AArch64

/-- Copy the sixteen limbs. -/
def copy (o a : Nat) : List Instr :=
  (List.range 16).flatMap fun i => [ld .x4 (a + 8 * i), st .x4 (o + 8 * i)]

/-- One carry step, with the incoming carry in `x6`. -/
def carryStep (o a i : Nat) : List Instr :=
  [ld .x4 (a + 8 * i), .add .x .x4 .x4 .x6,
    .logic .and .x .x5 .x4 .x12, st .x5 (o + 8 * i), .lsr .x .x6 .x4 28]

def pass (o a : Nat) : List Instr :=
  .movz .x .x6 0 0 :: (List.range 16).flatMap (carryStep o a)

/-- Fold the carry into limbs 0 and 8. -/
def fold : List Instr :=
  [0, 8].flatMap fun i => [ld .x4 (TMP + 8 * i), .add .x .x4 .x4 .x6, st .x4 (TMP + 8 * i)]

def normalize (o : Nat) : List Instr :=
  pass TMP TMP ++ fold ++ pass TMP TMP ++ fold ++ pass o TMP

/-- Add a product to the current row, whose base is `x10`. -/
def rowStep (b j : Nat) : List Instr :=
  [ld .x4 (b + 8 * j), .ldr .x .x5 .x10 (ACC + 8 * j),
    .madd .x .x4 .x4 .x6 .x5, .str .x .x4 .x10 (ACC + 8 * j)]

def rowHead (a : Nat) : List Instr := [.ldr .x .x6 .x10 a]

def rowTail : List Instr :=
  [.addImm .x .x10 .x10 8, .addImm .x .x9 .x9 1, .subImm .x .x11 .x9 16]

def row (a b : Nat) : List Instr := rowHead a ++ (List.range 16).flatMap (rowStep b) ++ rowTail

def reduceCol (k : Nat) : List Instr :=
  [ld .x4 (ACC + 8 * k), ld .x5 (ACC + 8 * (k + 16)), .add .x .x4 .x4 .x5] ++
  (if k < 8 then [ld .x5 (ACC + 8 * (k + 24)), .add .x .x4 .x4 .x5]
   else [ld .x5 (ACC + 8 * (k + 8)), .add .x .x4 .x4 .x5,
     ld .x5 (ACC + 8 * (k + 16)), .add .x .x4 .x4 .x5]) ++ [st .x4 (TMP + 8 * k)]

def mul (o a b : Nat) : Prog isa :=
  .seq (.block ([.movz .x .x4 0 0] ++
    (List.range 32).map (fun i => st .x4 (ACC + 8 * i)) ++
    [.movz .x .x9 0 0, .addImm .x .x10 .x3 0])) <|
  .seq (.loop (.block (row a b)) (.nonzero .x .x11)) <|
    .block ((List.range 16).flatMap reduceCol ++ normalize o)

/-- Limb `i` of `2p`. -/
def subK (i : Nat) : BitVec 16 := if i = 8 then 0xfffc else 0xfffe

def add (o a b : Nat) : List Instr :=
  (List.range 16).flatMap (fun i =>
    [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x4 .x4 .x5,
      st .x4 (TMP + 8 * i)]) ++ normalize o

def sub (o a b : Nat) : List Instr :=
  (List.range 16).flatMap (fun i =>
    [ld .x4 (a + 8 * i), .movz .x .x5 (subK i) 0, .movk .x .x5 0x1fff 1,
      .add .x .x4 .x4 .x5, ld .x5 (b + 8 * i), .sub .x .x4 .x4 .x5,
      st .x4 (TMP + 8 * i)]) ++ normalize o

def mulSmall (o a : Nat) : List Instr :=
  [.movz .x .x6 39081 0] ++ (List.range 16).flatMap (fun i =>
    [ld .x4 (a + 8 * i), .mul .x .x4 .x4 .x6, st .x4 (TMP + 8 * i)]) ++ normalize o

/-! Pointwise coefficients and their first carry pass share registers. -/
namespace Pointwise

def addEval (a b i : Nat) : List Instr :=
  [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x4 .x4 .x5]

def subEval (a b i : Nat) : List Instr :=
  [ld .x4 (a + 8 * i), .movz .x .x5 (subK i) 0, .movk .x .x5 0x1fff 1,
    .add .x .x4 .x4 .x5, ld .x5 (b + 8 * i), .sub .x .x4 .x4 .x5]

def smallEval (a i : Nat) : List Instr :=
  [ld .x4 (a + 8 * i), .movz .x .x5 39081 0, .mul .x .x4 .x4 .x5]

def carry (i : Nat) : List Instr :=
  [.add .x .x4 .x4 .x6, .logic .and .x .x5 .x4 .x12,
    st .x5 (TMP + 8 * i), .lsr .x .x6 .x4 28]

def finish (o : Nat) : List Instr := fold ++ pass TMP TMP ++ fold ++ pass o TMP

def fused (code : Nat → List Instr) (o : Nat) : List Instr :=
  [.movz .x .x6 0 0] ++ (List.range 16).flatMap (fun i => code i ++ carry i) ++ finish o

def add (o a b : Nat) : List Instr := fused (addEval a b) o
def sub (o a b : Nat) : List Instr := fused (subEval a b) o
def small (o a : Nat) : List Instr := fused (smallEval a) o

end Pointwise

/-- Swap two slots under the mask in `x6`. -/
def cswap (x y : Nat) : List Instr :=
  (List.range 16).flatMap fun i =>
    [ld .x4 (x + 8 * i), ld .x5 (y + 8 * i), .logic .eor .x .x7 .x4 .x5,
      .logic .and .x .x7 .x7 .x6, .logic .eor .x .x4 .x4 .x7,
      .logic .eor .x .x5 .x5 .x7, st .x4 (x + 8 * i), st .x5 (y + 8 * i)]

inductive Op
  | mul (o a b : Nat)
  | mulSmall (o a : Nat)
  | add (o a b : Nat)
  | sub (o a b : Nat)
  | copy (o a : Nat)
  deriving DecidableEq, Repr

def Op.code : Op → Prog isa
  | .mul o a b => Tail.mul o a b
  | .mulSmall o a => .block (Pointwise.small o a)
  | .add o a b => .block (Pointwise.add o a b)
  | .sub o a b => .block (Pointwise.sub o a b)
  | .copy o a => .block (AArch64.copy o a)

def ops : List Op → Prog isa
  | [] => .block []
  | o :: os => .seq o.code (ops os)

def stepOps : List Op :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB,
    .add C X3 Z3, .sub D X3 Z3, .mul DA D A, .mul CB C B,
    .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3, .mul Z3 X1 Z3,
    .mul X2 AA BB, .mulSmall Z2 E, .add Z2 AA Z2, .mul Z2 E Z2]

def stepHead : List Instr :=
  [.subImm .x .x19 .x19 1, .add .x .x11 .x3 .x19, .ldrb .x4 .x11 BITS,
    ld .x5 SWAP, .logic .eor .x .x5 .x5 .x4, st .x4 SWAP,
    .movz .x .x6 0 0, .sub .x .x6 .x6 .x5] ++ cswap X2 X3 ++ cswap Z2 Z3

def step : Prog isa := .seq (.block stepHead) (ops stepOps)

def ladder : Prog isa :=
  .seq (.block [.movz .x .x19 448 0]) (.loop step (.nonzero .x .x19))

def lastSwap : List Instr :=
  [ld .x5 SWAP, .movz .x .x6 0 0, .sub .x .x6 .x6 .x5] ++ cswap X2 X3 ++ cswap Z2 Z3

/-- Square `n` times in place, for `n > 0`. -/
def sqn (o n : Nat) : Prog isa :=
  .seq (.block [.movz .x .x19 (BitVec.ofNat 16 n) 0])
    (.loop (.seq (Tail.mul o o o) (.block [.subImm .x .x19 .x19 1])) (.nonzero .x .x19))

def invert : Prog isa :=
  .seq (ops [.copy T0 Z2]) <| .seq (sqn T0 1) <| .seq (ops [.mul T0 T0 Z2, .copy T1 T0]) <|
  .seq (sqn T1 2) <| .seq (ops [.mul T1 T1 T0, .copy T2 T1]) <|
  .seq (sqn T2 4) <| .seq (ops [.mul T2 T2 T1, .copy T3 T2]) <|
  .seq (sqn T3 8) <| .seq (ops [.mul T3 T3 T2, .copy T4 T3]) <|
  .seq (sqn T4 16) <| .seq (ops [.mul T4 T4 T3, .copy T5 T4]) <|
  .seq (sqn T5 32) <| .seq (ops [.mul T5 T5 T4, .copy T6 T5]) <|
  .seq (sqn T6 64) <| .seq (ops [.mul T6 T6 T5]) <|
  .seq (sqn T6 64) <| .seq (ops [.mul T6 T6 T5]) <|
  .seq (sqn T6 16) <| .seq (ops [.mul T6 T6 T3]) <|
  .seq (sqn T6 8) <| .seq (ops [.mul T6 T6 T2]) <|
  .seq (sqn T6 4) <| .seq (ops [.mul T6 T6 T1]) <|
  .seq (sqn T6 2) <| .seq (ops [.mul T6 T6 T0, .copy T7 T6]) <|
  .seq (sqn T7 1) <| .seq (ops [.mul T7 T7 Z2]) <|
  .seq (sqn T7 225) <| .seq (sqn T6 2) <| ops [.mul T6 T6 Z2, .mul T7 T7 T6]

/-- Decode seven bytes into two limbs without reading past the input. -/
def decodePair (i : Nat) : List Instr :=
  [.movz .x .x4 0 0] ++ (List.range 7).flatMap (fun j =>
    [.lsl .x .x4 .x4 8, .ldrb .x7 .x2 (7 * i + (6 - j)), .add .x .x4 .x4 .x7]) ++
  [.logic .and .x .x7 .x4 .x12, st .x7 (X1 + 16 * i), st .x7 (X3 + 16 * i),
    .lsr .x .x4 .x4 28, st .x4 (X1 + 16 * i + 8), st .x4 (X3 + 16 * i + 8)]

/-- One scalar byte, expanded into eight bits. -/
def bitsBody : List Instr :=
  [.add .x .x11 .x1 .x19, .ldrb .x4 .x11 0,
    .lsl .x .x11 .x19 3, .add .x .x11 .x3 .x11] ++
  (List.range 8).flatMap (fun j =>
    [.lsr .x .x5 .x4 j, .logic .and .x .x5 .x5 .x8, .strb .x5 .x11 (BITS + j)]) ++
  [.addImm .x .x19 .x19 1, .subImm .x .x11 .x19 56]

/-- Expand the scalar and apply the RFC 7748 clamp. -/
def bits : Prog isa :=
  .seq (.block [.movz .x .x19 0 0, .movz .x .x8 1 0])
    (.seq (.loop (.block bitsBody) (.nonzero .x .x11))
      (.block [.movz .x .x4 0 0, .strb .x4 .x3 BITS, .strb .x4 .x3 (BITS + 1),
        .movz .x .x4 1 0, .strb .x4 .x3 (BITS + 447)]))

/-- Initialize all slots except the decoded coordinate. -/
def initSlots : List Instr :=
  [.movz .x .x4 0 0] ++
  (List.range 32).map (fun i => st .x4 (X2 + 8 * i)) ++
  (List.range 288).map (fun i => st .x4 (Z3 + 8 * i)) ++
  [st .x4 SWAP, .movz .x .x4 1 0, st .x4 X2, st .x4 Z3]

def setup : List Instr :=
  [st .x19 0, st .x20 8, .addImm .x .x20 .x0 0,
    .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
  (List.range 8).flatMap decodePair ++ initSlots

/-- Add `1 + 2^224`: its carry is one exactly when `[X2] >= p`. -/
def freeze : List Instr :=
  copy TMP X2 ++ [0, 8].flatMap (fun i =>
    [ld .x4 (TMP + 8 * i), .addImm .x .x4 .x4 1, st .x4 (TMP + 8 * i)]) ++ pass TMP TMP ++
  [.movz .x .x7 0 0, .sub .x .x7 .x7 .x6] ++
  (List.range 16).flatMap fun i =>
    [ld .x4 (X2 + 8 * i), ld .x5 (TMP + 8 * i), .logic .eor .x .x5 .x5 .x4,
      .logic .and .x .x5 .x5 .x7, .logic .eor .x .x4 .x4 .x5, st .x4 (X2 + 8 * i)]

/-- Pack two limbs into seven output bytes. -/
def packPair (i : Nat) : List Instr :=
  [ld .x4 (X2 + 16 * i + 8), .lsl .x .x4 .x4 28,
    ld .x5 (X2 + 16 * i), .add .x .x4 .x4 .x5] ++
  (List.range 7).flatMap fun j => [.strb .x4 .x1 (7 * i + j), .lsr .x .x4 .x4 8]

def finish : Prog isa :=
  .seq (Tail.mul X2 X2 T7) (.block (freeze ++ (List.range 8).flatMap packPair ++ [ld .x19 0, ld .x20 8]))

def x448 : Prog isa :=
  .seq (.block setup) <| .seq bits <| .seq (.block [.addImm .x .x1 .x20 0]) <|
    .seq ladder <| .seq (.block lastSwap) <| .seq invert finish

end VG.Impl.X448.AArch64
