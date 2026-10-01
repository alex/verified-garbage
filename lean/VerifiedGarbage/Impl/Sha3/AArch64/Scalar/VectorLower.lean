import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lower

namespace VG.Impl.Sha3.AArch64.Scalar
open VG VG.AArch64

/-- Caller-saved vectors used for the two temporary lanes. -/
def slotV (k : Nat) : VReg := if k = 0 then .v24 else .v25

/-- Keep temporary lanes in vectors instead of scratch memory. -/
def lowerVector : ScalarOp → List Instr
  | .spill k a => [.vop (.dup .d2 (slotV k) a)]
  | .reload d k => [.umov .x d (slotV k) 0]
  | op => lower op

def vectorCoreInstrs : List Instr := coreOps.flatMap lowerVector

end VG.Impl.Sha3.AArch64.Scalar
