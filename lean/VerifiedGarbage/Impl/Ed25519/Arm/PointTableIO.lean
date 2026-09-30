import VerifiedGarbage.Impl.Ed25519.Arm.Packed

/-! Fixed workspace addresses for the packed verification points. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def scratchAddr (o : Nat) : List Instr :=
  [.movw .r12 (BitVec.ofNat 16 o), .dp .add .r12 .r0 (.reg .r12)]
def pointTableWrite (o : Nat) : List Instr := scratchAddr o ++ pointToTable
def pointTableRead (o : Nat) : List Instr := scratchAddr o ++ pointFromTable

end VG.Impl.Ed25519.Arm
