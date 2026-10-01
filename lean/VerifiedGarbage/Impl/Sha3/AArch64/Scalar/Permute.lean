import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Boundary
import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Control
import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lower

namespace VG.Impl.Sha3.AArch64.Scalar
open VG VG.AArch64

/-- Register-resident scalar Keccak: one counted round core, preserving the
frameless generic sponge calling convention. -/
def permute : Prog isa := Boundary.wrap (Control.middle coreInstrs)

end VG.Impl.Sha3.AArch64.Scalar
