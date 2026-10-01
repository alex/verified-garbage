import VerifiedGarbage.TCB.Arm.Isa

/-!
# X448: ARMv7 implementation

Field elements are twenty-eight 16-bit limbs in 32-bit words. Each
multiplication row propagates carries so that every multiply and addition
fits in a word. Reduction uses `2^448 = 2^224 + 1` modulo the field prime.
Only baseline instructions are used, including the low-word `mul`.

`r0` holds the working space, `r12` the output pointer, `r11` the ladder
or squaring counter, and `r6` the limb mask. Registers `r4` through `r11`
are saved in the working space and restored before returning.
-/

namespace VG.Impl.X448.Arm

open VG.Arm

def ld (r : Reg) (d : Nat) : Instr := .ldr r .r0 d
def st (r : Reg) (d : Nat) : Instr := .str r .r0 d

/-- Slots reserve 128 bytes, of which 112 hold the limbs. -/
def slot (n : Nat) : Nat := 64 + 128 * n
def X1 : Nat := slot 0
def X2 : Nat := slot 1
def Z2 : Nat := slot 2
def X3 : Nat := slot 3
def Z3 : Nat := slot 4
def A : Nat := slot 5
def B : Nat := slot 6
def C : Nat := slot 7
def D : Nat := slot 8
def AA : Nat := slot 9
def BB : Nat := slot 10
def E : Nat := slot 11
def DA : Nat := slot 12
def CB : Nat := slot 13
def T0 : Nat := slot 14
def T1 : Nat := slot 15
def T2 : Nat := slot 16
def T3 : Nat := slot 17
def T4 : Nat := slot 18
def T5 : Nat := slot 19
def T6 : Nat := slot 20
def T7 : Nat := slot 21
def SWAP : Nat := 32
def BITS : Nat := 3072
def ACC : Nat := 3584
def TMP : Nat := 3840

/-- Copy the twenty-eight limbs. -/
def copy (o a : Nat) : List Instr :=
  (List.range 28).flatMap fun i => [ld .r3 (a + 4 * i), st .r3 (o + 4 * i)]

/-- Carry the sum in `r3` and the incoming carry in `r5`. -/
def carryStep (rb : Reg) (o : Nat) : List Instr :=
  [.dp .add .r3 .r3 (.reg .r5), .dp .and .r4 .r3 (.reg .r6), .str .r4 rb o,
    .mov .r5 (.shifted .r3 .lsr 16)]

/-- Carry twenty-eight sums supplied by `src`. -/
def carryPass (rb : Reg) (o : Nat) (src : Nat → List Instr) : List Instr :=
  (List.range 28).flatMap fun i => src i ++ carryStep rb (o + 4 * i)

def pass (o a : Nat) : List Instr :=
  [.mov .r5 (.imm 0)] ++ carryPass .r0 o (fun i => [ld .r3 (a + 4 * i)])

/-- Fold the carry into limbs 0 and 14. -/
def fold : List Instr :=
  [0, 14].flatMap fun i => [ld .r3 (TMP + 4 * i), .dp .add .r3 .r3 (.reg .r5), st .r3 (TMP + 4 * i)]

def normalize (o : Nat) : List Instr := pass TMP TMP ++ fold ++ pass TMP TMP ++ fold ++ pass o TMP

/-- One word of a multiplication row. -/
def rowStep (b j : Nat) : List Instr :=
  [ld .r2 (b + 4 * j), .mul .r2 .r1 .r2, .ldr .r3 .r7 (ACC + 4 * j),
    .dp .add .r3 .r3 (.reg .r2)] ++ carryStep .r7 (ACC + 4 * j)

def row (a b : Nat) : List Instr :=
  [.ldr .r1 .r7 a, .mov .r5 (.imm 0)] ++ (List.range 28).flatMap (rowStep b) ++
  [.str .r5 .r7 (ACC + 112), .dp .add .r7 .r7 (.imm 4), .subs .r9 .r9 (.imm 1)]

def reduceCol (k : Nat) : List Instr :=
  [ld .r3 (ACC + 4 * k), ld .r2 (ACC + 4 * (k + 28)), .dp .add .r3 .r3 (.reg .r2)] ++
  (if k < 14 then [ld .r2 (ACC + 4 * (k + 42)), .dp .add .r3 .r3 (.reg .r2)]
   else [ld .r2 (ACC + 4 * (k + 14)), .dp .add .r3 .r3 (.reg .r2),
     ld .r2 (ACC + 4 * (k + 28)), .dp .add .r3 .r3 (.reg .r2)]) ++ [st .r3 (TMP + 4 * k)]

/-- Initialize the first half of the product; each row writes the next carry word. -/
def zeroAcc : List Instr :=
  [.mov .r3 (.imm 0)] ++ (List.range 28).flatMap fun i => [st .r3 (ACC + 4 * i)]

def mulPre : List Instr := zeroAcc ++ [.mov .r7 (.reg .r0), .mov .r9 (.imm 28)]

def mul (o a b : Nat) : Prog isa :=
  .seq (.block mulPre) <|
  .seq (.loop (.block (row a b)) .ne) <|
    .block ((List.range 28).flatMap reduceCol ++ normalize o)

/-- The low word of limb `i` of twice the prime; its high bit is added separately. -/
def subK (i : Nat) : BitVec 16 := if i = 14 then 0xfffc else 0xfffe

def add (o a b : Nat) : List Instr :=
  (List.range 28).flatMap (fun i =>
    [ld .r3 (a + 4 * i), ld .r2 (b + 4 * i), .dp .add .r3 .r3 (.reg .r2),
      st .r3 (TMP + 4 * i)]) ++ normalize o

def sub (o a b : Nat) : List Instr :=
  (List.range 28).flatMap (fun i =>
    [ld .r3 (a + 4 * i), .movw .r2 (subK i), .dp .add .r2 .r2 (.imm 65536),
      .dp .add .r3 .r3 (.reg .r2), ld .r2 (b + 4 * i), .dp .sub .r3 .r3 (.reg .r2),
      st .r3 (TMP + 4 * i)]) ++ normalize o

def mulSmall (o a : Nat) : List Instr :=
  [.movw .r5 39081] ++ (List.range 28).flatMap (fun i =>
    [ld .r3 (a + 4 * i), .mul .r3 .r3 .r5, st .r3 (TMP + 4 * i)]) ++ normalize o

/-- Swap under the mask in `r5`. -/
def cswap (x y : Nat) : List Instr :=
  (List.range 28).flatMap fun i =>
    [ld .r3 (x + 4 * i), ld .r2 (y + 4 * i), .dp .eor .r4 .r3 (.reg .r2),
      .dp .and .r4 .r4 (.reg .r5), .dp .eor .r3 .r3 (.reg .r4),
      .dp .eor .r2 .r2 (.reg .r4), st .r3 (x + 4 * i), st .r2 (y + 4 * i)]

inductive Op
  | mul (o a b : Nat)
  | mulSmall (o a : Nat)
  | add (o a b : Nat)
  | sub (o a b : Nat)
  | copy (o a : Nat)
  deriving DecidableEq, Repr

def Op.code : Op → Prog isa
  | .mul o a b => Arm.mul o a b
  | .mulSmall o a => .block (Arm.mulSmall o a)
  | .add o a b => .block (Arm.add o a b)
  | .sub o a b => .block (Arm.sub o a b)
  | .copy o a => .block (Arm.copy o a)

def ops : List Op → Prog isa
  | [] => .block []
  | o :: os => .seq o.code (ops os)

def stepOps : List Op :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB,
    .add C X3 Z3, .sub D X3 Z3, .mul DA D A, .mul CB C B,
    .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3, .mul Z3 X1 Z3,
    .mul X2 AA BB, .mulSmall Z2 E, .add Z2 AA Z2, .mul Z2 E Z2]

def stepHead : List Instr :=
  [.dp .sub .r11 .r11 (.imm 1), .dp .add .r7 .r0 (.reg .r11), .ldrb .r3 .r7 BITS,
    ld .r2 SWAP, .dp .eor .r2 .r2 (.reg .r3), st .r3 SWAP,
    .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r2)] ++ cswap X2 X3 ++ cswap Z2 Z3

def stepBody : Prog isa := .seq (.block stepHead) (ops stepOps)

def step : Prog isa := .seq stepBody (.block [.cmp .r11 (.imm 0)])

def ladder : Prog isa := .seq (.block [.movw .r11 448]) (.loop step .ne)

def lastSwap : List Instr :=
  [ld .r2 SWAP, .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r2)] ++ cswap X2 X3 ++ cswap Z2 Z3

/-- Square `n` times in place, for positive `n`. -/
def sqn (o n : Nat) : Prog isa :=
  .seq (.block [.movw .r11 (BitVec.ofNat 16 n)])
    (.loop (.seq (mul o o o) (.block [.subs .r11 .r11 (.imm 1)])) .ne)

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

/-- Two byte loads decode a limb without requiring input alignment. -/
def decodeLimb (i : Nat) : List Instr :=
  [.ldrb .r3 .r2 (2 * i), .ldrb .r4 .r2 (2 * i + 1),
    .dp .add .r3 .r3 (.shifted .r4 .lsl 8), st .r3 (X1 + 4 * i), st .r3 (X3 + 4 * i)]

/-- Expand one scalar byte into eight individual bits. -/
def bitsBody : List Instr :=
  [.dp .add .r7 .r1 (.reg .r11), .ldrb .r3 .r7 0,
    .dp .add .r7 .r0 (.shifted .r11 .lsl 3)] ++
  (List.range 8).flatMap (fun j =>
    [.mov .r2 (if j = 0 then .reg .r3 else .shifted .r3 .lsr j),
      .dp .and .r2 .r2 (.imm 1), .strb .r2 .r7 (BITS + j)]) ++
  [.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.imm 56)]

def bits : Prog isa :=
  .seq (.block [.mov .r11 (.imm 0)]) <|
  .seq (.loop (.block bitsBody) .ne) <|
    .block [.mov .r3 (.imm 0), .strb .r3 .r0 BITS, .strb .r3 .r0 (BITS + 1),
      .mov .r3 (.imm 1), .strb .r3 .r0 (BITS + 447)]

/-- Initialize the other slots, retaining the decoded coordinate. -/
def initSlots : List Instr :=
  [.mov .r3 (.imm 0)] ++
  (List.range 64).map (fun i => st .r3 (X2 + 4 * i)) ++
  (List.range 576).map (fun i => st .r3 (Z3 + 4 * i)) ++
  [st .r3 SWAP, .mov .r3 (.imm 1), st .r3 X2, st .r3 Z3]

def saved : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

def setup : List Instr :=
  (List.range 8).map (fun i => .str (saved[i]!) .r3 (4 * i)) ++
  [.mov .r12 (.reg .r0), .mov .r0 (.reg .r3), .movw .r6 65535] ++
  (List.range 28).flatMap decodeLimb ++ initSlots

/-- Add `1 + 2^224`, then select the carried result when the carry is one. -/
def freeze : List Instr :=
  copy TMP X2 ++ [0, 14].flatMap (fun i =>
    [ld .r3 (TMP + 4 * i), .dp .add .r3 .r3 (.imm 1), st .r3 (TMP + 4 * i)]) ++ pass TMP TMP ++
  [.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r5)] ++
  (List.range 28).flatMap fun i =>
    [ld .r3 (X2 + 4 * i), ld .r2 (TMP + 4 * i), .dp .eor .r2 .r2 (.reg .r3),
      .dp .and .r2 .r2 (.reg .r4), .dp .eor .r3 .r3 (.reg .r2), st .r3 (X2 + 4 * i)]

def packLimb (i : Nat) : List Instr :=
  [ld .r3 (X2 + 4 * i), .strb .r3 .r12 (2 * i), .mov .r3 (.shifted .r3 .lsr 8),
    .strb .r3 .r12 (2 * i + 1)]

def finish : Prog isa :=
  .seq (mul X2 X2 T7) (.block (freeze ++ (List.range 28).flatMap packLimb ++
    (List.range 8).map fun i => ld (saved[i]!) (4 * i)))

def x448 : Prog isa :=
  .seq (.block setup) <| .seq bits <| .seq ladder <| .seq (.block lastSwap) <| .seq invert finish

end VG.Impl.X448.Arm
