import VerifiedGarbage.Impl.Ed25519.Arm.Field
import VerifiedGarbage.Spec.Ed25519

/-! Constants and copies in the field workspace. -/

namespace VG.Impl.Ed25519.Arm

open VG.Arm

def constPointOps (p : Spec.Ed25519.Point) : List FieldOp :=
  [.const 0 p.X, .const 1 p.Y, .const 2 p.Z, .const 3 p.T]

def constPoint (p : Spec.Ed25519.Point) : Prog isa := fieldCode (constPointOps p)

/-- Save the accumulator while a batch of powers is prepared. -/
def savePointOps : List FieldOp := [.copy 17 0, .copy 18 1, .copy 19 2, .copy 20 3]

def restorePointOps : List FieldOp := [.copy 0 17, .copy 1 18, .copy 2 19, .copy 3 20]

def copyPointToQOps : List FieldOp := [.copy 4 0, .copy 5 1, .copy 6 2, .copy 7 3]

def savePoint : Prog isa := fieldCode savePointOps

def restorePoint : Prog isa := fieldCode restorePointOps

def copyPointToQ : Prog isa := fieldCode copyPointToQOps

/-- Initialize every working field limb to zero. -/
def initFields : List Instr := [.mov .r3 (.imm 0)] ++ storeN .r3 64 352

end VG.Impl.Ed25519.Arm
