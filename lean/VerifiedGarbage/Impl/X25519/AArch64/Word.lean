import VerifiedGarbage.Impl.X25519.AArch64
import VerifiedGarbage.Impl.X25519.AArch64.Small
import VerifiedGarbage.Impl.Ed25519.AArch64.Field
import VerifiedGarbage.Impl.Ed25519.AArch64.Power
import VerifiedGarbage.Impl.Ed25519.AArch64.PointDecode

/-! Four-word X25519, sharing Ed25519's field operations and inversion. -/
namespace VG.Impl.X25519.AArch64.Word
open VG.AArch64
open VG.Impl.Ed25519.AArch64

abbrev ld := VG.Impl.Ed25519.AArch64.ld
abbrev st := VG.Impl.Ed25519.AArch64.st
abbrev cswap := VG.Impl.Ed25519.AArch64.cswap
abbrev freeze := VG.Impl.Ed25519.AArch64.freeze

abbrev SWAP : Nat := 768
abbrev OUT : Nat := 48
abbrev BITS : Nat := VG.Impl.X25519.AArch64.BITS

def setup : List Instr :=
  VG.Impl.X25519.AArch64.save ++ VG.Impl.X25519.AArch64.bits ++
  [VG.Impl.X25519.AArch64.st .x0 OUT, mov .x1 .x0, mov .x0 .x3] ++
  loadY ++ store4 (offset 0) ++
  fieldCode [.copy 3 0, .const 1 1, .const 2 0, .const 4 1, .const 18 121665] ++
  [.movz .x .x2 0 0, st .x2 SWAP]

def stepOps : List FieldOp := [
  .add 5 1 2, .sqr 9 5, .sub 6 1 2, .sqr 10 6, .sub 11 9 10,
  .add 7 3 4, .sub 8 3 4, .mul 12 8 5, .mul 13 7 6,
  .add 3 12 13, .sqr 3 3, .sub 4 12 13, .sqr 4 4, .mul 4 0 4,
  .mul 1 9 10, .mul 2 11 18, .add 2 9 2, .mul 2 11 2]

def stepPrefix : List Instr :=
  [.subImm .x .x19 .x19 1, .add .x .x8 .x0 .x19, .ldrb .x2 .x8 BITS,
    ld .x3 SWAP, st .x2 SWAP, .logic .eor .x .x3 .x3 .x2,
    .movz .x .x10 0 0, .sub .x .x3 .x10 .x3]

def stepHead : List Instr := stepPrefix ++
  cswap (offset 1) (offset 3) ++ cswap (offset 2) (offset 4)

def stepFields : List Instr := fieldCode (stepOps.take 15) ++
  VG.Impl.X25519.AArch64.mulA24 (offset 2) (offset 11) ++ fieldCode (stepOps.drop 16)

def step : List Instr := stepHead ++ stepFields

def ladder : Prog isa :=
  .seq (.block [.movz .x .x19 255 0]) (.loop (.block step) (.nonzero .x .x19))

def lastSwap : List Instr :=
  [ld .x3 SWAP, .movz .x .x10 0 0, .sub .x .x3 .x10 .x3] ++
  cswap (offset 1) (offset 3) ++ cswap (offset 2) (offset 4)

def finish : List Instr :=
  fieldMul (offset 1) (offset 1) (offset 15) ++ freeze (offset 1) ++
  [.str .x .x4 .x1 0, .str .x .x5 .x1 8,
    .str .x .x6 .x1 16, .str .x .x7 .x1 24] ++
  VG.Impl.Ed25519.AArch64.saved.map (fun (r,o) => ld r o)

def x25519 : Prog isa :=
  .seq (.block setup) <| .seq ladder <| .seq (.block lastSwap) <|
  .seq VG.Impl.Ed25519.AArch64.invert (.block finish)
end VG.Impl.X25519.AArch64.Word
