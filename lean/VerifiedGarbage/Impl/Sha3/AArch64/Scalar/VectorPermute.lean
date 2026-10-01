import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Boundary
import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Control
import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.VectorLower

namespace VG.Impl.Sha3.AArch64.Scalar
open VG VG.AArch64

/-- Alternative scalar permutation with both temporary lanes in vectors. -/
def vectorPermute : Prog isa := Boundary.wrap (Control.middle vectorCoreInstrs)

end VG.Impl.Sha3.AArch64.Scalar
