import VerifiedGarbage.Impl.Ed25519.Arm.FieldMemory

/-! Sixteen exact doublings, with a public counter in r10. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def doubleBody : Prog isa := .seq pointDouble (.block [.subs .r10 .r10 (.imm 1)])
def double16 : Prog isa := .seq (.block [.movw .r10 16]) (.loop doubleBody .ne)

end VG.Impl.Ed25519.Arm
