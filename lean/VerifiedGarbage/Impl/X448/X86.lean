import VerifiedGarbage.TCB.X86.Isa

/-!
# X448: x86 (32-bit) implementation

Field elements are twenty-eight 16-bit limbs in 32-bit words. A row of
products propagates its carry before the next row, keeping each sum below
2^32. Reduction uses `2^448 = 2^224 + 1` modulo the field prime.

Arguments use cdecl: output, scalar, point, and working space are at
`[esp + 4]` through `[esp + 16]`. The stack pointer does not move. `edi`
holds the working space and `esi` the ladder or squaring counter.
-/

namespace VG.Impl.X448.X86

open VG.X86

def at_ (r : Reg) (d : Nat) : MemOp := { base := r, disp := d }
def sc (d : Nat) : MemOp := at_ .edi d
def ld (r : Reg) (d : Nat) : Instr := .mov r (.mem (sc d))
def st (r : Reg) (d : Nat) : Instr := .store (sc d) r

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
  (List.range 28).flatMap fun i => [ld .eax (a + 4 * i), st .eax (o + 4 * i)]

/-- Carry the sum in `eax` and the incoming carry in `ebx`. -/
def carryStep (rb : Reg) (o : Nat) : List Instr :=
  [.alu .add .eax (.reg .ebx), .mov .edx (.reg .eax), .alu .and .edx (.imm 65535),
    .store (at_ rb o) .edx, .mov .ebx (.reg .eax), .shift .shr .ebx 16]

def carryPass (rb : Reg) (o : Nat) (src : Nat → List Instr) : List Instr :=
  (List.range 28).flatMap fun i => src i ++ carryStep rb (o + 4 * i)

def pass (o a : Nat) : List Instr :=
  [.mov .ebx (.imm 0)] ++ carryPass .edi o (fun i => [ld .eax (a + 4 * i)])

/-- Fold the carry into limbs 0 and 14. -/
def fold : List Instr :=
  [0, 14].flatMap fun i => [ld .eax (TMP + 4 * i), .alu .add .eax (.reg .ebx), st .eax (TMP + 4 * i)]

def normalize (o : Nat) : List Instr := pass TMP TMP ++ fold ++ pass TMP TMP ++ fold ++ pass o TMP

/-- One product of a multiplication row, added to the previous rows. -/
def rowStep (b j : Nat) : List Instr :=
  [ld .eax (b + 4 * j), .mul .ecx, .alu .add .eax (.mem (at_ .ebp (ACC + 4 * j)))] ++
    carryStep .ebp (ACC + 4 * j)

def row (a b : Nat) : List Instr :=
  [.mov .ecx (.mem (at_ .ebp a)), .mov .ebx (.imm 0)] ++ (List.range 28).flatMap (rowStep b) ++
  [.store (at_ .ebp (ACC + 112)) .ebx, .alu .add .ebp (.imm 4),
    .mov .edx (.reg .edi), .alu .add .edx (.imm 112), .alu .cmp .ebp (.reg .edx)]

def reduceCol (k : Nat) : List Instr :=
  [ld .eax (ACC + 4 * k), .alu .add .eax (.mem (sc (ACC + 4 * (k + 28))))] ++
  (if k < 14 then [.alu .add .eax (.mem (sc (ACC + 4 * (k + 42))))]
   else [.alu .add .eax (.mem (sc (ACC + 4 * (k + 14)))),
     .alu .add .eax (.mem (sc (ACC + 4 * (k + 28))))]) ++ [st .eax (TMP + 4 * k)]

def zeroAcc : List Instr :=
  [.mov .eax (.imm 0)] ++ (List.range 28).flatMap fun i => [st .eax (ACC + 4 * i)]

def mulPre : List Instr := zeroAcc ++ [.mov .ebp (.reg .edi)]

def mul (o a b : Nat) : Prog isa :=
  .seq (.block mulPre) <|
  .seq (.loop (.block (row a b)) .ne) <|
    .block ((List.range 28).flatMap reduceCol ++ normalize o)

/-- A coefficient of twice the prime. -/
def subK (i : Nat) : BitVec 32 := if i = 14 then 131068 else 131070

def add (o a b : Nat) : List Instr :=
  (List.range 28).flatMap (fun i =>
    [ld .eax (a + 4 * i), .alu .add .eax (.mem (sc (b + 4 * i))), st .eax (TMP + 4 * i)]) ++ normalize o

def sub (o a b : Nat) : List Instr :=
  (List.range 28).flatMap (fun i =>
    [ld .eax (a + 4 * i), .alu .add .eax (.imm (subK i)),
      .alu .sub .eax (.mem (sc (b + 4 * i))), st .eax (TMP + 4 * i)]) ++ normalize o

def mulSmall (o a : Nat) : List Instr :=
  [.mov .ecx (.imm 39081)] ++ (List.range 28).flatMap (fun i =>
    [ld .eax (a + 4 * i), .mul .ecx, st .eax (TMP + 4 * i)]) ++ normalize o

/-- Swap under the mask in `ebx`. -/
def cswap (x y : Nat) : List Instr :=
  (List.range 28).flatMap fun i =>
    [ld .eax (x + 4 * i), ld .ecx (y + 4 * i), .mov .edx (.reg .eax), .alu .xor .edx (.reg .ecx),
      .alu .and .edx (.reg .ebx), .alu .xor .eax (.reg .edx), .alu .xor .ecx (.reg .edx),
      st .eax (x + 4 * i), st .ecx (y + 4 * i)]

inductive Op
  | mul (o a b : Nat)
  | mulSmall (o a : Nat)
  | add (o a b : Nat)
  | sub (o a b : Nat)
  | copy (o a : Nat)
  deriving DecidableEq, Repr

def Op.code : Op → Prog isa
  | .mul o a b => X86.mul o a b
  | .mulSmall o a => .block (X86.mulSmall o a)
  | .add o a b => .block (X86.add o a b)
  | .sub o a b => .block (X86.sub o a b)
  | .copy o a => .block (X86.copy o a)

def ops : List Op → Prog isa
  | [] => .block []
  | o :: os => .seq o.code (ops os)

def stepOps : List Op :=
  [.add A X2 Z2, .mul AA A A, .sub B X2 Z2, .mul BB B B, .sub E AA BB,
    .add C X3 Z3, .sub D X3 Z3, .mul DA D A, .mul CB C B,
    .add X3 DA CB, .mul X3 X3 X3, .sub Z3 DA CB, .mul Z3 Z3 Z3, .mul Z3 X1 Z3,
    .mul X2 AA BB, .mulSmall Z2 E, .add Z2 AA Z2, .mul Z2 E Z2]

def stepHead : List Instr :=
  [.alu .sub .esi (.imm 1), .mov .ebp (.reg .edi), .alu .add .ebp (.reg .esi),
    .movzx8 .eax (at_ .ebp BITS), ld .ecx SWAP, .alu .xor .ecx (.reg .eax), st .eax SWAP,
    .mov .ebx (.imm 0), .alu .sub .ebx (.reg .ecx)] ++ cswap X2 X3 ++ cswap Z2 Z3

def stepBody : Prog isa := .seq (.block stepHead) (ops stepOps)
def step : Prog isa := .seq stepBody (.block [.alu .cmp .esi (.imm 0)])
def ladder : Prog isa := .seq (.block [.mov .esi (.imm 448)]) (.loop step .ne)

def lastSwap : List Instr :=
  [ld .ecx SWAP, .mov .ebx (.imm 0), .alu .sub .ebx (.reg .ecx)] ++ cswap X2 X3 ++ cswap Z2 Z3

/-- Square `n` times in place, for positive `n`. -/
def sqn (o n : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.imm (BitVec.ofNat 32 n))])
    (.loop (.seq (mul o o o) (.block [.alu .sub .esi (.imm 1)])) .ne)

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
  [.movzx8 .eax (at_ .esi (2 * i)), .movzx8 .edx (at_ .esi (2 * i + 1)),
    .shift .ror .edx 24, .alu .add .eax (.reg .edx), st .eax (X1 + 4 * i), st .eax (X3 + 4 * i)]

def bitJ (i j : Nat) : List Instr :=
  [.mov .edx (.reg .eax)] ++ (if j = 0 then [] else [.shift .shr .edx j]) ++
    [.alu .and .edx (.imm 1), .store8 (sc (BITS + 8 * i + j)) .dl]

/-- Expand the scalar's bytes, then apply the RFC 7748 clamp. -/
def bits : Prog isa := .block <|
  [.mov .esi (.mem (at_ .esp 8))] ++
  ((List.range 56).flatMap fun i =>
    [.movzx8 .eax (at_ .esi i)] ++ (List.range 8).flatMap (bitJ i)) ++
  [.mov .edx (.imm 0), .store8 (sc BITS) .dl, .store8 (sc (BITS + 1)) .dl,
    .mov .edx (.imm 1), .store8 (sc (BITS + 447)) .dl]

def initSlots : List Instr :=
  [.alu .xor .eax (.reg .eax)] ++
  (List.range 64).map (fun i => st .eax (X2 + 4 * i)) ++
  (List.range 576).map (fun i => st .eax (Z3 + 4 * i)) ++
  [st .eax SWAP, .mov .eax (.imm 1), st .eax X2, st .eax Z3]

/-- Save through `eax` before replacing the working-space register. -/
def save : List Instr :=
  [.mov .eax (.mem (at_ .esp 16)), .store (at_ .eax 0) .ebx, .store (at_ .eax 4) .esi,
    .store (at_ .eax 8) .edi, .store (at_ .eax 12) .ebp, .mov .edi (.reg .eax)]

def setup : List Instr := save ++ [.mov .esi (.mem (at_ .esp 12))] ++
  (List.range 28).flatMap decodeLimb ++ initSlots

def freeze : List Instr :=
  copy TMP X2 ++ [0, 14].flatMap (fun i =>
    [ld .eax (TMP + 4 * i), .alu .add .eax (.imm 1), st .eax (TMP + 4 * i)]) ++ pass TMP TMP ++
  [.mov .ecx (.imm 0), .alu .sub .ecx (.reg .ebx)] ++
  (List.range 28).flatMap fun i =>
    [ld .eax (X2 + 4 * i), ld .edx (TMP + 4 * i), .alu .xor .edx (.reg .eax),
      .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx), st .eax (X2 + 4 * i)]

def packLimb (i : Nat) : List Instr :=
  [ld .eax (X2 + 4 * i), .store8 (at_ .esi (2 * i)) .al, .shift .shr .eax 8,
    .store8 (at_ .esi (2 * i + 1)) .al]

/-- Restore `edi` last, reading every saved register through `eax`. -/
def restore : List Instr :=
  [.mov .eax (.reg .edi), .mov .ebx (.mem (at_ .eax 0)), .mov .esi (.mem (at_ .eax 4)),
    .mov .ebp (.mem (at_ .eax 12)), .mov .edi (.mem (at_ .eax 8))]

def finish : Prog isa :=
  .seq (mul X2 X2 T7) (.block (freeze ++ [.mov .esi (.mem (at_ .esp 4))] ++
    (List.range 28).flatMap packLimb ++ restore))

def x448 : Prog isa :=
  .seq (.block setup) <| .seq bits <| .seq ladder <| .seq (.block lastSwap) <| .seq invert finish

end VG.Impl.X448.X86
