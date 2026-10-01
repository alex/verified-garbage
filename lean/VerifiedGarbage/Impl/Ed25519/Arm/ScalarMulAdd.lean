import VerifiedGarbage.Impl.Ed25519.Arm.ScalarABI

/-! Full-width multiply-add before subgroup-order reduction. -/
namespace VG.Impl.Ed25519.Arm
open VG VG.Arm

def scalarWideAdd (r : Nat) : List Instr :=
  [.movw .r6 65535, .mov .r5 (.imm 0)] ++ pass .r0 ACC (addSrc ACC r) ++
    pass .r0 (ACC + 64) (ldSrc (ACC + 64))

/-- The packed 512-bit product occupies bytes 512–575. -/
def scalarPackWide : List Instr :=
  [.dp .add .r12 .r0 (.imm 512)] ++ packField ACC 0 ++ packField (ACC + 64) 32

def scalarMulAddEngine : Prog isa :=
  .seq (scalarWideMul 128 192) <|
    .seq (.block (scalarWideAdd 64 ++ scalarPackWide))
      (.seq (.block [.mov .r8 (.reg .r10)]) scalarReduceEngine)

def scalarArgReg : Nat → Reg
  | 0 => .r0 | 1 => .r1 | 2 => .r2 | _ => .r3

def scalarStoreArgs : List Instr :=
  (List.range 4).flatMap fun i => [.str (scalarArgReg i) .r12 (32 + 4 * i)]

def scalarMulAddArgs : List Instr :=
  [.ldrSp .r12 0] ++ scalarSave .r12 ++ scalarStoreArgs ++ [.mov .r0 (.reg .r12)]

def scalarLoadInput (o ptrOff : Nat) : List Instr :=
  [.ldr .r12 .r0 ptrOff] ++ unpackField o 0

def scalarMulAddInputs : List Instr :=
  (List.range 3).flatMap (fun i => scalarLoadInput (64 + 64 * i) (36 + 4 * i)) ++ [.ldr .r10 .r0 32]

def scalarMulAddFinish : List Instr :=
  [.mov .r12 (.reg .r8)] ++ packField SR 0 ++ scalarRestore

def scalarMulAdd : Prog isa :=
  .seq (.block (scalarMulAddArgs ++ scalarMulAddInputs))
    (.seq scalarMulAddEngine (.block scalarMulAddFinish))

end VG.Impl.Ed25519.Arm
