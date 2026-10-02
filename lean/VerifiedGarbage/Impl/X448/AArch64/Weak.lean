import VerifiedGarbage.Impl.X448.AArch64
import VerifiedGarbage.Impl.Curve448.AArch64
namespace VG.Impl.X448.AArch64.Weak
open VG VG.AArch64 VG.Impl.X448.AArch64
abbrev cswap := VG.Impl.Curve448.AArch64.cswap

def code : Op → Prog isa
  | .mul o a b => Curve448.AArch64.mul o a b
  | .mulSmall o a => .block (Curve448.AArch64.small o a)
  | .add o a b => .block (Curve448.AArch64.add o a b)
  | .sub o a b => .block (Curve448.AArch64.sub o a b)
  | .copy o a => .block (Curve448.AArch64.copy o a)
def ops : List Op → Prog isa
  | [] => .block []
  | o :: os => .seq (code o) (ops os)
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
    (.loop (.seq (Curve448.AArch64.mul o o o) (.block [.subImm .x .x19 .x19 1])) (.nonzero .x .x19))

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


def convert : List Instr := (List.range 22).flatMap fun i => Curve448.AArch64.fromLegacy (slot i)
def setup : List Instr := AArch64.setup ++ convert

def finish : Prog isa := .seq (Curve448.AArch64.mul X2 X2 T7)
  (.block (Curve448.AArch64.toLegacy X2 ++ AArch64.freeze ++
    (List.range 8).flatMap AArch64.packPair ++ [ld .x19 0, ld .x20 8]))
def x448 : Prog isa :=
  .seq (.block setup) <| .seq AArch64.bits <| .seq (.block [.addImm .x .x1 .x20 0]) <|
    .seq ladder <| .seq (.block lastSwap) <| .seq invert finish
end VG.Impl.X448.AArch64.Weak
