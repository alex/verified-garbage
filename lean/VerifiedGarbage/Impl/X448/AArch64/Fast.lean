import VerifiedGarbage.Impl.X448.AArch64.Weak
import VerifiedGarbage.Impl.Curve448.AArch64.Fast
import VerifiedGarbage.Impl.Curve448.AArch64.Neon

/-!
# X448: AArch64 implementation with register-resident field arithmetic

`vg_x448(out = x0, scalar = x1, point = x2, scratch = x3)`, as
`Impl/X448/AArch64/Weak.lean`, with the field operations of
`Impl/Curve448/AArch64/Fast.lean`. They use `x21`–`x28`, which the function
saves in the working space with `x19` and `x20` and restores before
returning.

Each ladder step forms `A, B, C, D` from the unswapped coordinates
(`butterfly`): the swapped coordinates are not stored, since the step
overwrites all four. Four of its ten products are two pairs of AdvSIMD
multiplications (`Impl/Curve448/AArch64/Neon.lean`), each interleaved with
scalar operations independent of it, so that the vector and the integer
units run at once. The function saves `v8`–`v15` too.
-/

namespace VG.Impl.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64

/-- Where `x21`–`x28` are saved. -/
def SAVE : Nat := 3520

/-- Where `v8`–`v15` are saved, past the vector working space. -/
def VSAVE : Nat := 4736

def saved : Nat → Reg
  | 0 => .x21 | 1 => .x22 | 2 => .x23 | 3 => .x24 | 4 => .x25 | 5 => .x26 | 6 => .x27 | _ => .x28

/-- `[o] := [a] * [b]`, squaring when the operands are the same. -/
def fmul (o a b : Nat) : List Instr := if a = b then Curve448.AArch64.Fast.sqr o a else Curve448.AArch64.Fast.mul o a b

inductive Op
  | mul (o a b : Nat)
  | sub (o a b : Nat)
  | addSub (o₁ o₂ a b : Nat)
  | small (o a e : Nat)
  | copy (o a : Nat)
  deriving DecidableEq, Repr

def Op.code : Op → List Instr
  | .mul o a b => fmul o a b
  | .sub o a b => Curve448.AArch64.Fast.sub o a b
  | .addSub o₁ o₂ a b => Curve448.AArch64.Fast.addSub o₁ o₂ a b
  | .small o a e => Curve448.AArch64.Fast.small o a e
  | .copy o a => Curve448.AArch64.copy o a

def ops : List Op → Prog isa
  | [] => .block []
  | o :: os => .seq (.block o.code) (ops os)

def codeOf (l : List Op) : List Instr := l.flatMap Op.code

/-- Interleave `a` and `b`, keeping each at the same relative progress, `i`
instructions of `a` (of `n`) and `j` of `b` (of `m`) taken. -/
def weaveGo (n m : Nat) : Nat → Nat → Nat → List Instr → List Instr → List Instr
  | 0, _, _, a, b => a ++ b
  | _ + 1, _, _, [], b => b
  | _ + 1, _, _, x :: a, [] => x :: a
  | f + 1, i, j, x :: a, y :: b =>
    if i * m ≤ j * n then x :: weaveGo n m f (i + 1) j a (y :: b) else y :: weaveGo n m f i (j + 1) (x :: a) b

def weave (a b : List Instr) : List Instr := weaveGo a.length b.length (a.length + b.length) 0 0 a b

/-- `DA = D A` and `CB = C B` in AdvSIMD, beside `AA`, `BB`, `X2 = AA BB`,
`E = AA - BB` and `T2 = AA + a24 E`. -/
def stepA : List Instr :=
  weave (codeOf [.mul AA A A, .mul BB B B, .mul X2 AA BB, .sub E AA BB, .small T2 AA E])
    (Curve448.AArch64.Neon.mul2 DA D A CB C B)

/-- `Z2 = E T2` and `X3 = T0²` in AdvSIMD, beside `T1²` and `Z3 = X1 T1`. -/
def stepB : List Instr :=
  weave (codeOf [.mul T1 T1 T1, .mul Z3 X1 T1]) (Curve448.AArch64.Neon.mul2 Z2 E T2 X3 T0 T0)

/-- Read the scalar bit and form the swap mask in `x6`. -/
def stepPre : List Instr :=
  [.subImm .x .x19 .x19 1, .add .x .x11 .x3 .x19, .ldrb .x4 .x11 BITS,
    ld .x5 SWAP, .logic .eor .x .x5 .x5 .x4, st .x4 SWAP,
    .movz .x .x6 0 0, .sub .x .x6 .x6 .x5]

def step : Prog isa :=
  .seq (.block (stepPre ++ Curve448.AArch64.Fast.butterfly X2 Z2 X3 Z3 A B C D)) <|
    .seq (.block stepA) <| .seq (ops [.addSub T0 T1 DA CB]) (.block stepB)

def ladder : Prog isa :=
  .seq (.block [.movz .x .x19 448 0]) (.loop step (.nonzero .x .x19))

/-- Square `n` times in place, for `n > 0`. -/
def sqn (o n : Nat) : Prog isa :=
  .seq (.block [.movz .x .x19 (BitVec.ofNat 16 n) 0])
    (.loop (.block (Curve448.AArch64.Fast.sqr o o ++ [.subImm .x .x19 .x19 1])) (.nonzero .x .x19))

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

def save : List Instr := (List.range 8).map fun k => st (saved k) (SAVE + 8 * k)
def restore : List Instr := (List.range 8).map fun k => ld (saved k) (SAVE + 8 * k)
def vsave : List Instr := (List.range 8).map fun k => Curve448.AArch64.Neon.stq (8 + k) (VSAVE + 16 * k)
def vrestore : List Instr := (List.range 8).map fun k => Curve448.AArch64.Neon.ldq (8 + k) (VSAVE + 16 * k)

def setup : List Instr := Weak.setup ++ save ++ vsave

def finish : Prog isa :=
  .block (fmul X2 X2 T7 ++ Curve448.AArch64.toLegacy X2 ++ AArch64.freeze ++
    (List.range 8).flatMap AArch64.packPair ++ [ld .x19 0, ld .x20 8] ++ restore ++ vrestore)

def x448 : Prog isa :=
  .seq (.block setup) <| .seq AArch64.bits <| .seq (.block [.addImm .x .x1 .x20 0]) <|
    .seq ladder <| .seq (.block Weak.lastSwap) <| .seq invert finish

end VG.Impl.X448.AArch64.Fast
