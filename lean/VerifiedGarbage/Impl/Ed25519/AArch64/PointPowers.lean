import VerifiedGarbage.Impl.Ed25519.AArch64.PointTable

/-! A public counter in x19 counting up to a bound. -/
namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

/-- `x8` = `x19 - count`: nonzero while another power follows. -/
def powersLeft (count : Nat) : List Instr :=
  const64 .x8 (BitVec.ofNat 64 count) ++ [.sub .x .x8 .x19 .x8]

def powersNext (count : Nat) : List Instr := ([.addImm .x .x19 .x19 1] : List Instr) ++ powersLeft count

end VG.Impl.Ed25519.AArch64
