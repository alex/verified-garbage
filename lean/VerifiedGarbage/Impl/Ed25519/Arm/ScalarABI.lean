import VerifiedGarbage.Impl.Ed25519.Arm.Scalar
import VerifiedGarbage.Impl.Ed25519.Arm.Packed

/-! The zero-stack ARM ABI wrappers for scalar arithmetic. -/
namespace VG.Impl.Ed25519.Arm
open VG VG.Arm

abbrev scalarSavedReg := Impl.X25519.Arm.savedReg

def scalarSave (base : Reg) : List Instr :=
  (List.range 8).flatMap fun i => [.str (scalarSavedReg i) base (4 * i)]

def scalarRestore : List Instr :=
  (List.range 8).flatMap fun i => [.ldr (scalarSavedReg i) .r0 (4 * i)]

def scalarReduceSetup : List Instr :=
  scalarSave .r2 ++ [.str .r0 .r2 32, .mov .r0 (.reg .r2), .mov .r12 (.reg .r1)]

def scalarFinish : List Instr :=
  [.ldr .r12 .r0 32] ++ packField SR 0 ++ scalarRestore

def scalarReduce : Prog isa :=
  .seq (.block scalarReduceSetup) (.seq scalarReduceEngine (.block scalarFinish))

end VG.Impl.Ed25519.Arm
