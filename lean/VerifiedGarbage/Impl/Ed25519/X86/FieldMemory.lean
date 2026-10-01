import VerifiedGarbage.Impl.Ed25519.X86.Field
import VerifiedGarbage.Spec.Ed25519

/-! Constants and copies in the field workspace. -/

namespace VG.Impl.Ed25519.X86

open VG.X86

def constPointOps (p : Spec.Ed25519.Point) : List FieldOp :=
  [.const 0 p.X, .const 1 p.Y, .const 2 p.Z, .const 3 p.T]

def constPoint (p : Spec.Ed25519.Point) : List Instr := fieldCode (constPointOps p)

/-- Save the accumulator while a batch of powers is prepared. -/
def savePointOps : List FieldOp := [.copy 17 0, .copy 18 1, .copy 19 2, .copy 20 3]

def restorePointOps : List FieldOp := [.copy 0 17, .copy 1 18, .copy 2 19, .copy 3 20]

def copyPointToQOps : List FieldOp := [.copy 4 0, .copy 5 1, .copy 6 2, .copy 7 3]

def savePoint : List Instr := fieldCode savePointOps

def restorePoint : List Instr := fieldCode restorePointOps

def copyPointToQ : List Instr := fieldCode copyPointToQOps

end VG.Impl.Ed25519.X86
